The files in this folder contain functions related to enforcing opacity using the reactive synthesis tool BoSy (https://github.com/reactive-systems/bosy)

Some modifications must be made to the base BoSy installation so that it uses a Buchi automaton we construct, instead of converting an LTL specification to a Buchi automaton.

There are two changed files in the swift_files folder within this directory that must be copied into the BoSy installation:
- Conversion.swift should be copied into {bosy_path}/Sources/Automata/Conversion.swift (overwriting the existing file)
- main.swift should be copied into {bosy_path}/Sources/BoSyHyper/main.swift (overwriting the existing file)

The main function to perform run the full synthesis process is run_bosy() in bosy_interface.py
