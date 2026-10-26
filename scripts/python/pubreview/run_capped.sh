#!/bin/bash
# Runs a review script under a 4 GB address-space cap with single-threaded BLAS.
# numpy's OpenBLAS hangs at import under the cap when it starts one thread per CPU.
ulimit -v 4194304
export OPENBLAS_NUM_THREADS=1 OMP_NUM_THREADS=1
cd "$(dirname "$0")"
exec python3 -u "$@"
