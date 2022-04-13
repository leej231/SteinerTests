import numpy as np
import gurobipy as gp
from gurobipy import GRB
import matplotlib.pyplot as plt
import ast
from timeit import default_timer as timer

start = timer()

# extracting information from the .txt file
with open("C:\\Users\jaemyeongl\Desktop\FSTs\output.txt",'r') as file:
    fileinfo = file.read().splitlines()

# no. of vertices
n = int(fileinfo[0])
# location of each terminal
terminals = ast.literal_eval(fileinfo[1])
# number of Steiner points in each hyperedge
S = ast.literal_eval(fileinfo[2])
# length of each hyperedge
L = ast.literal_eval(fileinfo[3])
# terminals in each hyperedge
T = ast.literal_eval(fileinfo[4])
# list of edges
topologies = ast.literal_eval(fileinfo[5])
# number of iterations
iter = 1

milp_model = gp.Model("milp")
milp_model.Params.LogToConsole = 0

# limit on the total number of Steiner points
kk = 1

# number of hyperedges
h = len(S)
print(h)

x = milp_model.addVars(h, vtype=GRB.BINARY)

milp_model.setObjective(sum(L[i] * x[i] for i in range(h)), GRB.MINIMIZE)
c2 = milp_model.addConstr(sum(S[i] * x[i] for i in range(h)) <= kk)

milp_model.optimize()

xvalues = np.zeros((h), dtype=int)
for i in range(h):
    xvalues[i] = x[i].x

print(xvalues)

components = [i for i in range(n)]

def find(lst, a):
    return [i for i, x in enumerate(lst) if x == a]

hypertree = find(xvalues, 1)
for i in range(len(hypertree)):
    currenthyper = hypertree[i]
    vincurrenthyper = T[currenthyper]

    comps = [components[i] for i in vincurrenthyper]
    aa = len(comps)
    compsnodouble = list(set(comps))
    ab = len(compsnodouble)

    nextitcomp = np.min(compsnodouble)

    for j in range(ab):
        if nextitcomp != compsnodouble[j]:
            tempind = find(components, compsnodouble[j])
            for k in tempind:
                components[k] = nextitcomp

# number of comps in the current graph
noofcomps = len(list(set(components)))

print(components)

while noofcomps > 1.5:

    iter = iter + 1
    # labels of different components
    l = list(set(components))
    p = len(l)
    dfjeqns = np.zeros((p, h), dtype=int)

    for i in range(h):
        currenth = T[i]

        for j in range(p):
            # currentcompv denotes all vertices in the current component
            currentcompv = find(components, l[j])
            # notcurrentcompv denotes all vertices not in the current component
            notcurrentcompv = list(set(range(n)) - set(currentcompv))

            if len(set(currentcompv)-set(currenth)) < len(currentcompv) and \
                    len(set(notcurrentcompv) - set(currenth)) < len(notcurrentcompv):

                dfjeqns[j, i] = 1


    milp_model.addConstrs(sum(x[i] * dfjeqns[j, i] for i in range(h)) >= 1 for j in range(p))
    milp_model.optimize()

    xvalues = np.zeros((h), dtype=int)
    for i in range(h):
        xvalues[i] = x[i].x

    print(xvalues)

    components = [i for i in range(n)]

    hypertree = find(xvalues, 1)
    for i in range(len(hypertree)):
        currenthyper = hypertree[i]
        vincurrenthyper = T[currenthyper]

        comps = [components[i] for i in vincurrenthyper]
        aa = len(comps)
        compsnodouble = list(set(comps))
        ab = len(compsnodouble)

        nextitcomp = np.min(compsnodouble)

        for j in range(ab):
            if nextitcomp != compsnodouble[j]:
                tempind = find(components, compsnodouble[j])
                for k in tempind:
                    components[k] = nextitcomp

    # number of comps in the current graph
    noofcomps = len(list(set(components)))

    print(components)

htree = find(xvalues, 1)
print(htree)
print(iter)

def count(l):
    return sum(1 + count(i) for i in l if isinstance(i,list))

fig, ax = plt.subplots()
for i in range(len(htree)):
    a = htree[i]
    he = topologies[a]
    c = count(he)
    if c == 2:
        plt.plot([he[0][0], he[1][0]], [he[0][1], he[1][1]], 'r')
    else:
        for j in range(len(he)):
            e = he[j]
            plt.plot([e[0][0], e[1][0]], [e[0][1], e[1][1]], 'b')

plt.xlim([-0.05, 1.05])
plt.ylim([-0.05, 1.05])
ax.set_aspect('equal')

for i in range(n):
    plt.scatter(terminals[i][0], terminals[i][1], c = 'k')
plt.show()


end = timer()
print(end - start)