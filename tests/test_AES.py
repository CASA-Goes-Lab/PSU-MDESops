import sys
sys.path.append('../')

import DESops as d

G = d.Automata("models/ex3AES.fsm")

# G.plot()
d.write_AES_SMV_model(G,"modelsSMV/ex3AES.smv")

