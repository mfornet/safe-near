#!/usr/bin/env bash
# Summarise a testsuite report: totals per outcome, then every .wast file
# that has a non-pass outcome. This is the quick "where are we" view of the
# interpreter's spec coverage.
#
# Usage: scripts/testsuite-summary.sh [REPORT]   (default: testsuite_report.txt)
#
# Outcomes: `pass` is a command that behaved as the spec says. `skipped:*`,
# `decode_error` and `module_unavailable` are unimplemented features, not
# regressions. `fail`, `interpreter_error` and `out_of_fuel` are real bugs.
set -euo pipefail

ROOT="$(cd "$(dirname "${BASH_SOURCE[0]}")/.." && pwd)"
report="${1:-$ROOT/testsuite_report.txt}"

total=$(wc -l < "$report" | tr -d ' ')
files=$(awk '{split($1, a, ":"); print a[1]}' "$report" | sort -u | wc -l | tr -d ' ')
passed=$(awk '$3 == "pass"' "$report" | wc -l | tr -d ' ')
clean_files=$(awk '{split($1, a, ":"); f[a[1]] = 1; if ($3 != "pass") bad[a[1]] = 1}
                   END {n = 0; for (k in f) if (!(k in bad)) n++; print n}' "$report")

echo "== $report"
echo "commands: $passed / $total pass"
echo "files:    $clean_files / $files fully passing"
echo
echo "== outcomes"
awk '{c[$3]++} END {for (k in c) printf "%7d  %s\n", c[k], k}' "$report" | sort -rn
echo
echo "== files with non-pass outcomes (count, file, outcome)"
awk '$3 != "pass" {split($1, a, ":"); c[a[1] "  " $3]++}
     END {for (k in c) printf "%5d  %s\n", c[k], k}' "$report" | sort -k2
