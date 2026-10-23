#!/usr/bin/env bash
# Run the linked stack client on the runtime and check what `client_adequate`
# says (criterion S4.3): the stack module is registered as "stack", the client
# is instantiated against it, which runs `main` as its start function, and
# the client's global `answer` then holds 20. A second client instance gets a
# fresh stack on a new page and answers 20 too.
#
# The script is built from the committed .wat files and run by the runtime's
# testsuite runner, so it needs ../wasm built (`lake build testsuite` there).
set -euo pipefail
cd "$(dirname "$0")/.."

runner=../wasm/.lake/build/bin/testsuite
if [ ! -x "$runner" ]; then
    echo "build the runner first: (cd ../wasm && lake build testsuite)" >&2
    exit 2
fi

dir="$(mktemp -d)"
trap 'rm -rf "$dir"' EXIT
{
    sed 's/^(module/(module $stack/' WasmLogic/Examples/Stack/stack.wat | grep -v '^;;'
    echo '(register "stack" $stack)'
    grep -v '^;;' WasmLogic/Examples/Client/client.wat
    echo '(assert_return (get "answer") (i32.const 20))'
    grep -v '^;;' WasmLogic/Examples/Client/client.wat
    echo '(assert_return (get "answer") (i32.const 20))'
} > "$dir/client.wast"
"$runner" --dir "$dir"
