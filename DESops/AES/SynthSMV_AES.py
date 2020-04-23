import igraph as ig
import subprocess
import os
from pathlib import Path

def write_AES_SMV_model(G,model_fname):
	create_SMV_file(G,model_fname)

	return

def create_SMV_file(G,model_fname):
	g = G._graph
	with open(model_fname, 'w') as f:
		print('MODULE unobservable_reach(Q,gamma,asg,obs)',file=f)
		print('VAR nx: array 0..{0} of boolean;'.format(g.vcount()-1),file=f)
		print('INIT (!nX[0]',end="",file=f)
		for i in range(g.vcount()-1):
			print('& !nx[{0}]'.format(i+1),end="",file = f)
		print(')',file=f)
		print('ASSIGN',file=f)

	return
