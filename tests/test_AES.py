import sys
sys.path.append('../')

import DESops as d

G = d.Automata("models/ex1AES.fsm")

# G.plot()
d.write_AES_SMV_model(G,"modelsSMV/ex1AES.smv")

