# flake8: noqa
# from DESops.automata.automata import _Automata

from DESops import SDA, random_DFA
from DESops.automata.DFA import DFA
from DESops.automata.event.event import Event
from DESops.automata.NFA import NFA
from DESops.automata.PFA import PFA
from DESops.basic_operations import composition, generic_functions, unary
from DESops.basic_operations.construct_complement import complement
from DESops.basic_operations.construct_reverse import reverse
from DESops.basic_operations.observer_comp import observer_comp
from DESops.basic_operations.parallel_comp import parallel_comp
from DESops.basic_operations.product_comp import product_comp
from DESops.file.fsm_to_bdd import read_fsm_to_bdd
from DESops.file.fsm_to_igraph import read_fsm
from DESops.file.igraph_pickle import *
from DESops.file.igraph_to_fsm import write_fsm
from DESops.generation.generate_automaton import generate_automaton
from DESops.opacity import opacity
from DESops.supervisory_control.AES.AES import construct_AES
from DESops.supervisory_control.supr_contr import supr_contr
from DESops.supervisory_control.supr_contr_norm import supr_contr_norm
from DESops.supervisory_control.VLPPO.VLPPO import offline_VLPPO
from DESops.visualization.plot import plot
from DESops.visualization.write_svg import write_svg

__version__ = "20.3.1"
