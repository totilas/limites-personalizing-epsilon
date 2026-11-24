#!/bin/sh
# The copies in this bridge must be identical to the main project's definitions.
cd "$(dirname "$0")" || exit 1
diff -u ../../lean/LimitesProofs/Renyi.lean LimitesProofs/Renyi.lean &&
diff -u ../../lean/LimitesProofs/Privacy/Defs.lean LimitesProofs/Privacy/Defs.lean &&
echo "In sync with ../../lean"
