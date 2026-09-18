This package provides a convenient way of handling Discrete Event System models as
finite state automata. Additionally, some useful functions and operations on automata have been
implemented, including parallel/product compositions and observer computation. The goal is to provide a simple way to combine these operations in a modular environment, with the usability of Python which makes extending the functionalities provided here very straightforward.

## Installation

DESops is installed with a plain Python virtual environment and `pip` — no extra package manager required.

### Step 1: Clone Repository

    $ git clone git@github.com:CASA-Goes-Lab/PSU-MDESops.git
    $ cd PSU-MDESops

### Step 2: Create and activate a virtual environment

Requires Python 3.11 or newer.

    $ python3 -m venv .venv
    $ source .venv/bin/activate        # Windows: .venv\Scripts\activate

### Step 3: Install DESops

    $ pip install --upgrade pip
    $ pip install "setuptools<81" wheel
    $ pip install --no-build-isolation -e ".[dev]"

The `setuptools<81` pin and `--no-build-isolation` flag work around the `dd` dependency (used for BDD support), which ships no prebuilt wheel and whose legacy `setup.py` still imports the now-removed `pkg_resources` module unless a compatible `setuptools` is already present in the environment.

`.[dev]` installs the test/lint tooling alongside DESops. For a minimal install without dev tools, drop `[dev]`. Two other optional extras are available:

    $ pip install --no-build-isolation -e ".[caching]"  # pycairo, for igraph's Cairo-based plotting
    $ pip install --no-build-isolation -e ".[docs]"      # Sphinx and friends, for building documentation

`pycairo` (the `caching` extra) additionally requires the system `pkg-config` and `cairo` libraries to be installed first — see [this guide](https://pycairo.readthedocs.io/en/latest/getting_started.html) for OS-specific instructions. Most users plotting with the default `plotly`-based visualization do not need this extra.

### Step 4: Using DESops

With the virtual environment active, verify the installation:

    $ python
    >>> import DESops as d
    >>> g = d.DFA()

Any IDE that supports selecting a Python interpreter (PyCharm, VS Code, etc.) can point directly at `.venv` for editing and running the project.

Once you have a working environment, you can follow the tutorials linked at the bottom of this page to get started using DESops.

#### Random Automata Generation

Generating random automata using the `random_DFA` submodule requires the REGAL software package, with source code bundled in this repository.
The following is only relevant for using the `random_DFA` submodule.
(link to DESops/random_DFA/regal-1.08.0929/COPYING) Some of the files in the library have been modified, so an external installation of the software won't work.

There are detailed instructions for compiling the source code in the file `random_DFA/regal-1.08.0929/regal_readme.txt`
There are several required libraries, and a c++ compiler is needed to build the REGAL executables. The script `build.py` (only for Linux systems with a g++ compiler) automates the build process after the preqrequisite libraries are installed.

#### Opacity enforcement

Two methods for synthesizing enforcement mechanisms for opacity are currently supported. The first requires the optional
python library [EdiSyn](https://gitlab.eecs.umich.edu/M-DES-tools/EdiSyn), which is not published to PyPI and must be
installed manually alongside DESops in the same virtual environment:

    $ git clone https://gitlab.eecs.umich.edu/M-DES-tools/EdiSyn.git
    $ pip install -e ./EdiSyn

The second method for opacity enforcement uses the library BoSy. See (/DESops/opacity/bosy) for more details.

## Documentation

The documentation for this project is hosted at [MDESops.github.io](https://MDESops.github.io) .
Documentation for most functions are provided as docstings in the code.
Additional documentation is managed by sphinx. To enable this, install with the `docs` extra: `pip install --no-build-isolation -e ".[docs]"`.
The documentation can then be built with the commands

    $ cd docs
    $ make html

View the documentation at `docs/build/html/index.html` with a web browser.

To update or add to the documentation, in the `docs` directory run the command

    $ make buildapi

Note that this generates new docs, overwriting existing docs.
Additionally, the documentation will need to be rebuilt after this step.

For now, the documentation must be manually added to the github.io web page.
Simply copy all files from ``docs/build/html/`` to the root directory of the github.io repository and push.

## Contributing to DESops

First, clone the repository using `git`:
```
$ git clone git@github.com:CASA-Goes-Lab/PSU-MDESops.git
$ cd PSU-MDESops
```

Second, follow the [Installation](#installation) steps above using the `.[dev]` extra, then install the `pre-commit` git hooks:
```
$ pre-commit install
```

### Before pushing your contribution to the repository

`pre-commit` checks the code style and fix it if necessary every time the code
changes are committed. When `pre-commit` fixes the code style, `git` automatically
reverts your `commit` command, so you will need to stage your changes again.

This repository employs [pytest](https://docs.pytest.org/en/latest/) to write tests.
All tests are located in `tests` directory, and must be written with the formats of
`pytest`.

You can execute tests by the following command:
```
$ pytest
```
You can also execute certain tests by specifying test names:
```
$ pytest -k [name]
```
For example, if you want to do the test defined by `def test_example():`, pass its name to `pytest` as:
```
$ pytest -k example
```

For other options of `pytest`, see `pytest --help`.

### Additional Resources

For tutorials, demonstrations, and further information about DESops, please check out the following resources:
- [Installation Tutorial](https://www.youtube.com/watch?v=xZAt-nGIQ-E)
- [DESops Tutorial 1](https://github.com/CASA-Goes-Lab/PSU-MDESops/blob/master/jupyter-tutorials/desops_tutorial_01.ipynb)
- [DESops Tutorial 2](https://github.com/CASA-Goes-Lab/PSU-MDESops/blob/master/jupyter-tutorials/desops_tutorial_02.ipynb)
- [Youtube Channel](https://www.youtube.com/channel/UCaoigOnm8eGMC7nslwd5-BA)
