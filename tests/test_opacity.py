import DESops as d
from DESops.opacity.opacity_verification import verify_joint_k_step_opacity, verify_separate_k_step_opacity

K = 1

g = d.Automata()
g.add_vertices(6, range(6))
g.add_edges([(0,1),(1,2),(2,3),(0,4),(4,5),(5,3)], labels=['u','a','a','a','u','a'])

g.vs['init'] = False
g.vs[0]['init'] = True

secret_states = [1,5]
g.vs['secret'] = False
g.vs[secret_states]['secret'] = True


Eo = ['a']
g.es['obs']=False
g.es.select(label_in=Eo)['obs'] = True
g.find_Euc_Euo()
Euo = g.Euo

print(verify_joint_k_step_opacity(g, K))
print(verify_separate_k_step_opacity(g, K))

g = d.Automata()
g.add_vertices(6, range(6))
g.add_edges([(0,1),(1,2),(2,3),(0,4),(4,5),(5,3)], labels=['u','a','a','a','u','a'])

g.vs['init'] = False
g.vs[0]['init'] = True

secret_states = [2,4]
g.vs['secret'] = False
g.vs[secret_states]['secret'] = True

Eo = ['a']
g.es['obs']=False
g.es.select(label_in=Eo)['obs'] = True
g.find_Euc_Euo()
Euo = g.Euo


print(verify_joint_k_step_opacity(g, K))
print(verify_separate_k_step_opacity(g, K))

