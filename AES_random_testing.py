import DESops as d
import time
import random

start = time.process_time()

AES_data = []
AES_c_data = []


import csv

def write_csv(filename, data):
    with open(filename, 'w') as file:
        writer = csv.writer(file)
        writer.writerow(["T reg (s)", "reg vc", "reg ec", "T compact (s)", "comp vc", "comp ec", "alphabet size", "crit state", "|Ec inter Eo|"])
        writer.writerows(data)

def read_csv(filename, data1, data2):
    with open(filename, 'r') as file:
        reader = csv.reader(file)
        for row in reader:
            data1.append(row[0:3])
            data2.append(row[3:6])

init_time = time.process_time()
crit_states = []


c = 5 # Euc prop (divide by 10 to get proportion of Euc)
o = 5
v = 200
a = 10
n = 10
for _ in range(n):
    g = d.random_DFA.generate(v, a, timeout=60, Euc_p=c / 10, Euo_p=o / 10, overlap=True)    
    print(len(g.Euc))
    print(len(g.Euo))
    print("---")
    # randomly select X_crit:
    X_crit = set()
    x = str(random.randint(0, v-1))
    X_crit.add(x)
    crit_states.append(x)

    # Ec intersection Eo is empty
    contr = {e for e in g.events if e not in g.Euc}
    obs = {e for e in g.events if e not in g.Euo}
    intersection = contr.intersection(obs)

    # only one controllable and observable
    
    start_time = time.process_time()
    A = d.construct_AES(g, X_crit, compact=False)  
    data = [time.process_time() - start_time, A.vcount(), A.ecount()]

    start_time = time.process_time()
    A = d.construct_AES(g, X_crit, compact=True)
    data.extend((time.process_time() - start_time, A.vcount(), A.ecount(), a, x, len(intersection)))
    AES_data.append(data)
    print(_)
print(time.process_time() - init_time)
write_csv("data/aes_test_c{0}_o{1}_v{2}_a{3}_n{4}.csv".format(c, o, v, a, n), AES_data)
