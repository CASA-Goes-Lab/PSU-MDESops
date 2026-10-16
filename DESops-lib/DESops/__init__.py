# flake8: noqa
# from DESops.core.automata import _Automata

from importlib.metadata import PackageNotFoundError
from importlib.metadata import version as _version

from DESops import error, random_automata
from DESops import sda as SDA
from DESops.core.automaton import Automaton
from DESops.core.dfa import DFA
from DESops.core.event import Event
from DESops.core.nfa import NFA
from DESops.core.pfa import PFA
from DESops.core.operations import composition, generic_functions, unary
from DESops.core.operations.complement import complement
from DESops.core.operations.reverse import reverse
from DESops.core.operations.language_equivalence import compare_language
from DESops.io.fsm_to_bdd import read_fsm_to_bdd
from DESops.io.fsm_to_igraph import read_fsm
from DESops.io.fsm import read_automaton, write_automaton
from DESops.io.cif import parse_cif, read_cif
from DESops.io.igraph_pickle import *
from DESops.io.igraph_to_fsm import write_fsm
from DESops.opacity import opacity_verification
from DESops.supervisory_control import supervisor
from DESops.visualization.plot import plot
from DESops.visualization.write_svg import write_svg
from DESops.visualization import dot
from DESops.diagnosis import diagnoser

try:
    __version__ = _version("DESops")
except PackageNotFoundError:
    __version__ = "0.0.0+unknown"
