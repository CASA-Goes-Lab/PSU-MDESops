# MDESops

Tools for modeling and analyzing Discrete Event Systems. The repository has two parts:

- **[`DESops-lib/`](DESops-lib/)**: the `DESops` Python library. The implementations live here, including the
  Nagini-verified cores (planned, in `DESops/verified/`). Installation and usage: [DESops-lib/README.md](DESops-lib/README.md).
- **[`DESops-proof/`](DESops-proof/)**: Lean 4 proofs of the algorithms implemented in `DESops-lib`, plus notes that
  match each Lean definition to the postconditions of the corresponding Nagini-verified Python function. See
  [DESops-proof/README.md](DESops-proof/README.md).

To install only the library, without cloning the repository:

    $ pip install "setuptools<81" wheel
    $ pip install --no-build-isolation "git+https://github.com/CASA-Goes-Lab/PSU-MDESops.git@v2#subdirectory=DESops-lib"

License: [license.txt](license.txt).
