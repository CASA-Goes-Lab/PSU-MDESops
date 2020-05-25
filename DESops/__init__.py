# flake8: noqa
#from DESops.automata.automata import _Automata

from DESops.automata.DFA import DFA
from DESops.automata.PFA import PFA
from DESops.automata.NFA import NFA

from DESops.automata.event.event import Event

from DESops.file.fsm_to_igraph import read_fsm
from DESops.file.igraph_to_fsm import write_fsm
from DESops.visualization.write_svg import write_svg
from DESops.file.igraph_pickle import *

from DESops.visualization.plot import plot

from DESops.basic_operations.parallel_comp import parallel_comp
from DESops.basic_operations.product_comp import product_comp
from DESops.basic_operations.observer_comp import observer_comp

from DESops.supervisory_control.supr_contr import supr_contr
from DESops.supervisory_control.supr_contr_norm import supr_contr_norm

__version__ = "20.3.1"
