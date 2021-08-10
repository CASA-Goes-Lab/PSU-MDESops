# flake8: noqa
# from DESops.automata.automata import _Automata

from DESops import SDA, error, random_automata
from DESops.automata.DFA import DFA
from DESops.automata.event import Event
from DESops.automata.NFA import NFA
from DESops.automata.PFA import PFA
from DESops.basic_operations import composition, generic_functions, unary
from DESops.basic_operations.construct_complement import complement
from DESops.basic_operations.construct_reverse import reverse
from DESops.basic_operations.language_equivalence import compare_language
from DESops.file.fsm_to_bdd import read_fsm_to_bdd
from DESops.file.fsm_to_igraph import read_fsm
from DESops.file.igraph_pickle import *
from DESops.file.igraph_to_fsm import write_fsm
from DESops.opacity import opacity
from DESops.supervisory_control import supervisor
from DESops.visualization.plot import plot
from DESops.visualization.write_svg import write_svg
from DESops.diagnoser import diagnoser

__version__ = "20.6.1a4"
