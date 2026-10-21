# MDESops (legacy)

The original `DESops` Python library and its repository-level config (`.editorconfig`, `.mailmap`,
`.pre-commit-config.yaml`), kept for reference and for comparison tests. New development happens
in [`../certisc-lib/`](../certisc-lib/) (`certisc`) and [`../certisc-proof/`](../certisc-proof/).

- **[`DESops-lib/`](DESops-lib/)**: the `DESops` Python library, including its own copy of the
  Nagini-verified checker in `DESops/verified/`. Installation and usage: [DESops-lib/README.md](DESops-lib/README.md).

To install only the legacy library, without cloning the repository:

    $ pip install "setuptools<81" wheel
    $ pip install --no-build-isolation "git+https://github.com/CASA-Goes-Lab/PSU-MDESops.git@v2#subdirectory=legacy/DESops-lib"

License: [license.txt](license.txt).
