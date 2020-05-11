"""
Constructs a new automata of the same inherited type as input
e.g. 
>>> input = d.DFA()
>>> new_input = d.construct_automata(input)
>>> type(new_input) # DFA
"""

from DESops.automata.DFA import DFA
from DESops.automata.PFA import PFA
from DESops.automata.NFA import NFA

def construct_automata(G):
    if isinstance(G, DFA):
        return DFA()
    if isinstance(G, PFA):
        return PFA()
    if isinstance(G, NFA):
        return NFA()