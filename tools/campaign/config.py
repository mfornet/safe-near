"""Profiles: which backend and model serve each role, and what to use when a
subscription or an API balance runs out.

A profile maps every role to a chain of tiers; the first tier is tried first
and the later ones are the escalation (section 11.2 of the proof plan). A
profile also names fallback profiles. When a backend is marked exhausted, its
tiers are skipped and the same role's tiers from the fallback profiles are
appended, so the campaign keeps running on what is left."""

from __future__ import annotations

from dataclasses import dataclass
from datetime import datetime, timedelta, timezone
import json
import os
from pathlib import Path

ROOT = Path(__file__).resolve().parents[2]
DEFAULT_PROFILES = ROOT / "tools/campaign/profiles.json"
STATE_DIR = ROOT / "campaign/.state"
ROLES = ("architect", "auditor", "prover", "grinder", "runner", "integrator")


@dataclass(frozen=True)
class Tier:
    backend: str
    model: str | None = None
    attempts: int = 2

    @property
    def label(self) -> str:
        return f"{self.backend}:{self.model or 'default'}"


class ConfigError(ValueError):
    pass


class Config:
    def __init__(self, data: dict, path: Path | None = None):
        self.path = path
        self.backends: dict[str, dict] = data.get("backends", {})
        self.profiles: dict[str, dict] = data.get("profiles", {})
        self.reset_hours: float = float(data.get("exhaustion_reset_hours", 5))
        self.default_profile: str = data.get("default_profile", "default")
        self.validate()

    @classmethod
    def load(cls, path: Path = DEFAULT_PROFILES) -> "Config":
        return cls(json.loads(Path(path).read_text()), Path(path))

    def validate(self) -> None:
        if not self.backends:
            raise ConfigError("no backends")
        for name, spec in self.backends.items():
            if spec.get("kind") not in ("claude-cli", "codex-cli", "openai-api", "fake", "fake-agent"):
                raise ConfigError(f"backend {name}: unknown kind {spec.get('kind')!r}")
        if self.default_profile not in self.profiles:
            raise ConfigError(f"default profile {self.default_profile!r} is not defined")
        for name, profile in self.profiles.items():
            for fallback in profile.get("fallbacks", []):
                if fallback not in self.profiles:
                    raise ConfigError(f"profile {name}: unknown fallback profile {fallback!r}")
            roles = profile.get("roles", {})
            for role in roles:
                if role not in ROLES:
                    raise ConfigError(f"profile {name}: unknown role {role!r}")
            for role in ROLES:
                if role not in roles or not roles[role]:
                    raise ConfigError(f"profile {name}: role {role!r} has no tier")
                for tier in roles[role]:
                    if tier.get("backend") not in self.backends:
                        raise ConfigError(f"profile {name}, role {role}: unknown backend {tier.get('backend')!r}")
                    if int(tier.get("attempts", 2)) < 1:
                        raise ConfigError(f"profile {name}, role {role}: attempts must be positive")

    def tiers(self, profile: str, role: str) -> list[Tier]:
        return [Tier(t["backend"], t.get("model"), int(t.get("attempts", 2)))
                for t in self.profiles[profile]["roles"][role]]

    def chain(self, role: str, profile: str | None = None, exhausted: set[str] = frozenset()) -> list[Tier]:
        """The tiers to try for `role`: the profile's, then its fallbacks', skipping
        exhausted backends and repeated tiers. Empty when nothing is left."""
        profile = profile or self.default_profile
        if profile not in self.profiles:
            raise ConfigError(f"unknown profile {profile!r}")
        seen, order = set(), []
        queue = [profile]
        while queue:
            name = queue.pop(0)
            if name in seen:
                continue
            seen.add(name)
            order.append(name)
            queue.extend(self.profiles[name].get("fallbacks", []))
        chain: list[Tier] = []
        for name in order:
            for tier in self.tiers(name, role):
                if tier.backend in exhausted or tier in chain:
                    continue
                chain.append(tier)
        return chain


class ExhaustionState:
    """Backends whose subscription or balance ran out, with the time the mark
    expires. Kept in a file so parallel runs and later runs see it."""

    def __init__(self, path: Path = STATE_DIR / "exhausted.json", reset_hours: float = 5):
        self.path = path
        self.reset_hours = reset_hours

    def _read(self) -> dict[str, str]:
        try:
            return json.loads(self.path.read_text())
        except (OSError, ValueError):
            return {}

    def active(self, now: datetime | None = None) -> set[str]:
        now = now or datetime.now(timezone.utc)
        live = set()
        for backend, until in self._read().items():
            try:
                if datetime.fromisoformat(until) > now:
                    live.add(backend)
            except ValueError:
                continue
        return live

    def mark(self, backend: str, now: datetime | None = None) -> datetime:
        now = now or datetime.now(timezone.utc)
        until = now + timedelta(hours=self.reset_hours)
        data = self._read()
        data[backend] = until.isoformat()
        self.path.parent.mkdir(parents=True, exist_ok=True)
        self.path.write_text(json.dumps(data, indent=2) + "\n")
        return until

    def clear(self, backend: str | None = None) -> None:
        if backend is None:
            if self.path.exists():
                self.path.unlink()
            return
        data = self._read()
        data.pop(backend, None)
        self.path.parent.mkdir(parents=True, exist_ok=True)
        self.path.write_text(json.dumps(data, indent=2) + "\n")


def api_key(spec: dict) -> str | None:
    return os.environ.get(spec.get("api_key_env", ""), "") or None
