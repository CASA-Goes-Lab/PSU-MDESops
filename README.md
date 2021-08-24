This package provides a convenient way of handling Discrete Event System models as
finite state automata. Additionally, some useful functions and operations on automata have been
implemented, including parallel/product compositions and observer computation. The goal is to provide a simple way to combine these operations in a modular environment, with the usability of Python which makes extending the functionalities provided here very straightforward.

## Installation

Below is a diagram that showcases the installation process. Before installing DESops, the first three steps must be completed first.  

![README_diagram graph image](img/diagram.png)

### Step 1: Clone Repository

On the right hand corner of this page, click on the blue box that says `Clone`. Copy and paste the HTTPS url. 

In your working directory, write the following command:

    $ git clone https://gitlab.eecs.umich.edu/M-DES-tools/desops.git

After running this command, a copy of this repository will be available in your working directory. 

### Step 2: Install pkg-config and cairo

These packages are dependencies required to install `pycairo`. This is key for the later installation of `python-igraph`, which DESops uses to plot graphs.

Both `pkg-config` and `cairo` can be installed at once. Depending on your operating system, you can follow the steps on this [website](https://pycairo.readthedocs.io/en/latest/getting_started.html) to properly install these dependencies. Do **NOT** install pycairo yet. This will be done in step 4.

### Step 3: Install Poetry:

The recommended way to install poetry is writing the following commands in your terminal:

### osx / linux / bashonwindows install instructions

    $ curl -sSL https://raw.githubusercontent.com/python-poetry/poetry/master/install-poetry.py | python3 -

### windows powershell install instructions

    $ curl -sSL https://raw.githubusercontent.com/python-poetry/poetry/master/install-poetry.py | python3 -

If this method does not work, you can use `pip` to properly install `poetry`. Run the following command:

    $ pip install --user poetry

### Common Error: Operating device does not recognize pip

Sometimes pip requires a different command depending on your operating system. If the command above did not work, try the following alternatives:

    $ python3 -m pip install --user poetry
or

    $ python -m pip install --user poetry

More information and different installation methods are available on the [poetry](https://python-poetry.org/) website if needed.

### Step 4: Install DESops:

Make sure you are in the same working directory as the `poetry.lock` file. This should be located where you cloned the repository.

DESops can be installed using [poetry](https://python-poetry.org/) and running the command:

    $ poetry install

pycairo is used by `python-igraph` for plotting Graphs. `DESops` uses these methods for plotting as well.
To use the `DESops.plot` submodule, install with pycairo as well:

    $ poetry install -E pycairo

### Common Error: Pycairo not recognized

If poetry **does not** recognize pycairo as an optional dependency, try running these two commands:

    $ poetry remove pycairo

Removes pycairo from the list of dependencies.

    $ poetry add "pycairo==1.11.1"

Note that version 1.11.1 of pycairo was specified due to issues with pycairo's current version 1.20
### Note for Windows Users:

When using Windows, pycairo needs to be built from the wheel. Download one of the "cp38" versions located here:
https://www.lfd.uci.edu/~gohlke/pythonlibs/#pycairo

Then install using `pip install <path_to>\pycairo‑1.19.1‑cp38‑cp38‑<win_version>.whl`

#### Random Automata Generation

Generating random automata using the `random_DFA` submodule requires the REGAL software package, with source code bundled in this repository.
The following is only relevant for using the `random_DFA` submodule.
(link to DESops/random_DFA/regal-1.08.0929/COPYING) Some of the files in the library have been modified, so an external installation of the software won't work.

There are detailed instructions for compiling the source code in the file `random_DFA/regal-1.08.0929/regal_readme.txt`
There are several required libraries, and a c++ compiler is needed to build the REGAL executables. The script `build.py` (only for Linux systems with a g++ compiler) automates the build process after the preqrequisite libraries are installed.

## Contributing to DESops

You will need [Poetry](https://python-poetry.org/) to start contribution on the DESops codes.

First, you will need to clone the repository using `git`:
```
$ git clone git@gitlab.eecs.umich.edu:M-DES-tools/desops.git
$ cd desops
```

Second, you will need to install the required dependencies and `pre-commit` git hooks:
```
$ poetry install
$ poetry run pre-commit install
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
$ poetry run pytest
```
You can also execute certain tests by specifying test names:
```
$ poetry run pytest -k [name]
```
For example, if you want to do the test defined by `def test_example():`, pass its name to `pytest` as:
```
$ poetry run pytest -k example
```

For other options of `pytest`, see `poetry run pytest --help`.
