The files in this folder contain functions related to enforcing opacity using the reactive synthesis tool BoSy (https://github.com/reactive-systems/bosy)

The main function to perform run the full synthesis process is run_bosy() in bosy_interface.py

Some modifications must be made to the base BoSy installation so that it uses a Buchi automaton we construct, instead of converting an LTL specification to a Buchi automaton.

### BoSy Installation
In an directory external to M-DESops, clone the correct commit of BoSy with
    $ git clone https://github.com/reactive-systems/bosy.git
    $ git checkout 2bad0d853e1b023aa27a6a0d8f8a129b5bd96ed7

Copy the file `bosy_patch.patch` in this directory of M-DESops into the newly created `bosy/` directory.
In the `bosy/` directory, apply the patch with the command
    $ git apply bosy_patch.patch

Next, BoSy can be installed as usual. See instructions at https://github.com/reactive-systems/bosy. If the necessary dependencies (i.e. swift) are installed, this can typically be done with the command `make`.
