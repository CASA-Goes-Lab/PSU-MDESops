import sys
sys.path.append('../')

import DESops as d

G = d.Automata("models/ex3AES.fsm")
P = d.parallel_comp([G,G])
P.plot()
