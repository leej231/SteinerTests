import math, random
from shapely import *
from shapely.geometry import Point, MultiPoint
from shapely.geometry.polygon import Polygon, LinearRing, LineString
from itertools import combinations
from scipy.spatial import Delaunay
import time
import matplotlib.pyplot as plt
 

def findangle(p1,p2): #finds angle in degrees of p2 from p1, 0 degrees is parallel to the x-axis, to the right, degrees between -180 and 180
	rise = p2[1] - p1[1]
	run = p2[0] - p1[0]
	if run == 0:
		if rise == 0:
			return 
		if rise > 0:
			return 90
		if rise < 0:
			return 270
	else:
		return math.degrees(math.atan(rise/run))
		
def rotatedpoint(p1, p2, angle): #rotates p2 around p1 by given angle
    qx = p1[0] + math.cos(math.radians(angle)) * (p2[0] - p1[0]) - math.sin(math.radians(angle)) * (p2[1] - p1[1])
    qy = p1[1] + math.sin(math.radians(angle)) * (p2[0] - p1[0]) + math.cos(math.radians(angle)) * (p2[1] - p1[1])
    return [qx, qy] 

def pointdistance(p1,p2): 
    return math.sqrt((p1[0]-p2[0])**2 + (p1[1]-p2[1])**2)

def equipoint2(p1,p2):
    newpoint = rotatedpoint(p1,p2,60)
    angle1 = findangle(newpoint,p1)
    angle2 = findangle(newpoint,p2)
    if angle1 < -120 and angle2 > 120:
        angle1 = angle1 + 360
    if angle2 < -120 and angle1 > 120:
        angle2 = angle2 + 360
    return [newpoint[0],newpoint[1],[p1,p2],min(angle1,angle2),max(angle1,angle2)]

def equipoint3(p1,p2,p3):
    a = pointdistance(p1,p2)
    b = pointdistance(p1,p3)
    c = pointdistance(p3,p2)
    biggest = max(a,b,c)
    if biggest == a:
        angle1 = findangle(p3,p1)
        angle2 = findangle(p3,p2)
        if angle1 < -120 and angle2 > 120:
            angle1 = angle1 + 360
        if angle2 < -120 and angle1 > 120:
            angle2 = angle2 + 360
        return [p3[0],p3[1],[p3,p1,p2],min(angle1,angle2),max(angle1,angle2)]
    if biggest == b:
        angle1 = findangle(p2,p1)
        angle2 = findangle(p2,p3)
        if angle1 < -120 and angle2 > 120:
            angle1 = angle1 + 360
        if angle2 < -120 and angle1 > 120:
            angle2 = angle2 + 360
        return [p2[0],p2[1],[p2,p1,p3],min(angle1,angle2),max(angle1,angle2)]
    if biggest == c:
        angle1 = findangle(p1,p2)
        angle2 = findangle(p1,p3)
        if angle1 < -120 and angle2 > 120:
            angle1 = angle1 + 360
        if angle2 < -120 and angle1 > 120:
            angle2 = angle2 + 360
        return [p1[0],p1[1],[p1,p2,p3],min(angle1,angle2),max(angle1,angle2)]
  
def getAngle(a, b, c): #finds angle between these three points at b
    ang = math.degrees(math.atan2(c[1]-b[1], c[0]-b[0]) - math.atan2(a[1]-b[1], a[0]-b[0]))
    if ang < 0:
        return ang + 360 
    else:
        return ang
    
def findIntersection(A,B,C,D):
    px= ( (A[0]*B[1]-A[1]*B[0])*(C[0]-D[0])-(A[0]-B[0])*(C[0]*D[1]-C[1]*D[0]) ) / ( (A[0]-B[0])*(C[1]-D[1])-(A[1]-B[1])*(C[0]-D[0]) ) 
    py= ( (A[0]*B[1]-A[1]*B[0])*(C[1]-D[1])-(A[1]-B[1])*(C[0]*D[1]-C[1]*D[0]) ) / ( (A[0]-B[0])*(C[1]-D[1])-(A[1]-B[1])*(C[0]-D[0]) )
    return [px, py]
  
def steiner(A,B,C):
    a = getAngle(B,A,C)
    b = getAngle(C,B,A)
    c = getAngle(A,C,B)
    w = max(a,b,c)
    if w >= 120:
        if w == a:
            return A
        elif w == b:
            return B
        else: 
            return C
    else:
        if LinearRing([A,B,C]).is_ccw:
            return findIntersection(C,rotatedpoint(B,A,60),B,rotatedpoint(A,C,60))
        else: 
            return findIntersection(B,rotatedpoint(C,A,60),C,rotatedpoint(A,B,60))
    
def distconstraint(p1,p2,p3): # Marcus conjecture where n=1/(2*sqrt(3) . Formula straight from wiki page on point to a line with small modifications. p3 is the point we are checking the distance from the interval p1-p2
    return abs((p2[0]-p1[0])*(p1[1]-p3[1]) - (p1[0]-p3[0])*(p2[1]-p1[1])) <= (1/(2*math.sqrt(3)))*((p2[0]-p1[0])**2 + (p2[1]-p1[1])**2)
      
def reversedist(p1,p2,p3): #p3 is the point we are checking distance from interval p1-p2
    m = 1/(2*math.sqrt(3))
    return (((1-2*m**2)/(2*m))*((p2[0]-p1[0])**2 + (p2[1]-p1[1])**2) <  abs((p2[0]-p1[0])*(p1[1]-p3[1]) - (p1[0]-p3[0])*(p2[1] - p1[1])))

def luneconstraint(p1,p2,p3): # returns true if p3 is inside the lune of p1 and p2
    return ((pointdistance(p3,p2) <= pointdistance(p1,p2)) and (pointdistance(p3,p1) <= pointdistance(p1,p2)))
    
def quadconstraint(p1,p2,p3): # returns true if p3 is inside the quad of p1 and p2
    quad = Polygon([p1,rotatedpoint(p1, p2, 60),p2,rotatedpoint(p2, p1, 60)])
    if quad.contains(Point(p3)):
        return False
    else:
        return True

def verticalconstraint(p1,p2,p3,p4): #check if p3,p4 is in Jae's vertical constraint made by p1,p2.
    if p1[1] == p2[1]:
        return (min(p1[0],p2[0]) <= p3[0] <= max(p1[0],p2[0])) and (min(p1[0],p2[0]) <= p4[0] <= max(p1[0],p2[0]))
    else:
        m = -(p1[0]-p2[0])/(p1[1]-p2[1])
        return (min(p1[1]-m*p1[0],p2[1]-m*p2[0]) <= p3[1] - m*p3[0] <= max(p1[1]-m*p1[0],p2[1]-m*p2[0])) and (min(p1[1]-m*p1[0],p2[1]-m*p2[0]) <= p4[1] - m*p4[0] <= max(p1[1]-m*p1[0],p2[1]-m*p2[0]))

def FindTerminals(list1):
    terminallist = []
    for i in list1:
        if not any(isinstance(j, list) for j in i):
            terminallist.append(i)
        else:
            terminallist.extend(FindTerminals(i))
    return terminallist


times = []
test_inputs = [6] #range(6,13)
r = 1 # number of repeats
for n in test_inputs:
        
    start_time = time.time()

    k = 1 #k in k-Steiner problem
    for i in range(r):
        terminals = []

        for i in range(n): # randomly generates points, of form (x,y,<lowest allowed angle>,<highest allowed angle>)
            newpoint = [random.random(),random.random(),[],-180,180]
            terminals.append(newpoint)


        branch_set = [] # general data structure for branches: list with [location,topology,angles] 
        branch_set.extend(terminals)

        tri = Delaunay([(points[0],points[1]) for points in terminals]) #finding Delaunay triangulation 

        edge_set = []
        for simplex in tri.simplices:
            edge_set.append([simplex[0],simplex[1]])
            edge_set.append([simplex[1],simplex[2]])
            edge_set.append([simplex[2],simplex[0]])
            
        for i in edge_set:
            i.sort()
        cleanlist = []
        [cleanlist.append(x) for x in edge_set if x not in cleanlist]

        fst_set = [[0, pointdistance(terminals[i],terminals[j]), [terminals[i][:2], terminals[j][:2]]] for [i,j] in cleanlist] #first element of list is number of steiner points, second is length

        for combo in combinations(terminals,2):
            branch_set.extend([equipoint2(combo[0],combo[1]),equipoint2(combo[1],combo[0])])
            
        for combo in combinations(terminals,3):
            polygon = Polygon([point[:2] for point in combo])
            polygonempty = True
            for j in terminals:
                if polygon.contains(Point(j)):
                    polygonempty = False
                    break
            if polygonempty:
                if (not distconstraint(combo[0],combo[1],combo[2]) or not distconstraint(combo[1],combo[0],combo[2])) or not distconstraint(combo[2],combo[1],combo[0]):
                    if (not reversedist(combo[0],combo[1],combo[2]) or not reversedist(combo[1],combo[0],combo[2])) or not reversedist(combo[2],combo[1],combo[0]):   
                        branch_set.append(equipoint3(combo[0],combo[1],combo[2]))
            
        for branch_pair in combinations(branch_set,2):
            if len(branch_pair[0][2])+len(branch_pair[1][2]) == 2:
                if len(branch_pair[0][2]) == 0:
                    s = findangle(branch_pair[1][:2],branch_pair[0][:2])
                    
                    a = branch_pair[0][:2]
                    b = branch_pair[1][2][0][:2]
                    c = branch_pair[1][2][1][:2]
                    if branch_pair[1][3] < s % 360 < branch_pair[1][4]: #if the point is in the cone
                        steiner_point = steiner(a,b,c)
                        if steiner_point not in [a,b,c]:
                            lunesempty = True
                            for j in terminals: #check lune constraint using proposed edges
                                if ((luneconstraint(a,steiner_point,j) or luneconstraint(b,steiner_point,j)) or luneconstraint(c,steiner_point,j)) and j[:2] not in [a,b,c]:
                                    lunesempty = False
                                    break
                            if lunesempty == True:
                                fst_set.append([1,pointdistance(branch_pair[1][:2],a),[[a,steiner_point],[b,steiner_point],[c,steiner_point]]])
                else: 
                    s = findangle(branch_pair[0][:2],branch_pair[1][:2])
                    
                    a = branch_pair[1][:2]
                    b = branch_pair[0][2][0][:2]
                    c = branch_pair[0][2][1][:2]
                    if branch_pair[0][3] < s % 360 < branch_pair[0][4]: #if the point is in the cone
                        steiner_point = steiner(a,b,c)
                        if steiner_point not in [a,b,c]:
                            lunesempty = True
                            for j in terminals: #check lune constraint using proposed edges
                                if ((luneconstraint(a,steiner_point,j) or luneconstraint(b,steiner_point,j)) or luneconstraint(c,steiner_point,j)) and j[:2] not in [a,b,c]:
                                    lunesempty = False
                                    break
                            if lunesempty == True:
                                fst_set.append([1,pointdistance(a,branch_pair[0][:2]),[[a,steiner_point],[b,steiner_point],[c,steiner_point]]])
            if len(branch_pair[0][2])+len(branch_pair[1][2]) == 3 and branch_pair[0][:2] != branch_pair[1][:2]:
                if len(branch_pair[0][2]) == 0:
                    s = findangle(branch_pair[1][:2],branch_pair[0][:2])
                    
                    a = branch_pair[1][2][0][:2]
                    b = branch_pair[0][:2]
                    c = branch_pair[1][2][1][:2]
                    d = branch_pair[1][2][2][:2]
                    if verticalconstraint(a,b,c,d) and verticalconstraint(c,d,a,b):
                        if (((branch_pair[1][3] < s % 360 < branch_pair[1][4]) and not distconstraint(c,d,b)) and not reversedist(c,d,b)) and luneconstraint(c,d,b): #if the point is in the cone, lune and distance constraints
                            if ((quadconstraint(a,b,c) and quadconstraint(a,b,d)) and quadconstraint(c,d,a)) and quadconstraint(c,d,b):    
                                cross_point = findIntersection(a,b,c,d)
                                lunesempty = True
                                for j in terminals: #check lune constraint using proposed edges
                                    if (((luneconstraint(a,cross_point,j) or luneconstraint(b,cross_point,j)) or luneconstraint(c,cross_point,j)) or luneconstraint(d,cross_point,j)) and j[:2] not in [a,b,c,d]:
                                        lunesempty = False
                                        break
                                if lunesempty == True:
                                    fst_set.append([1,pointdistance(a,b)+pointdistance(c,d),[[b,cross_point],[a,cross_point],[c,cross_point],[d,cross_point]]])
                else:
                    s = findangle(branch_pair[0][:2],branch_pair[1][:2])
                    
                    a = branch_pair[0][2][0][:2]
                    b = branch_pair[1][:2]
                    c = branch_pair[0][2][1][:2]
                    d = branch_pair[0][2][2][:2]
                    if verticalconstraint(a,b,c,d) and verticalconstraint(c,d,a,b):
                        if (((branch_pair[0][3] < s % 360 < branch_pair[0][4]) and not distconstraint(c,d,b)) and not reversedist(c,d,b)) and luneconstraint(c,d,b): #if the point is in the cone, lune and distance constraints
                            if ((quadconstraint(a,b,c) and quadconstraint(a,b,d)) and quadconstraint(c,d,a)) and quadconstraint(c,d,b):     
                                cross_point = findIntersection(a,b,c,d)
                                lunesempty = True
                                for j in terminals: #check lune constraint using proposed edges
                                    if (((luneconstraint(a,cross_point,j) or luneconstraint(b,cross_point,j)) or luneconstraint(c,cross_point,j)) or luneconstraint(d,cross_point,j)) and j[:2] not in [a,b,c,d]:
                                        lunesempty = False
                                        break
                                if lunesempty == True:
                                    fst_set.append([1,pointdistance(a,b)+pointdistance(c,d),[[b,cross_point],[a,cross_point],[c,cross_point],[d,cross_point]]])
                            
    
    times.append(((time.time() - start_time))/r)

print("--- %s seconds ---" % (time.time() - start_time))

# print(fst_set)

for i in fst_set:
    listofterminals = FindTerminals(i[2])
    terminalsbyindex = []
    for point in listofterminals:
        x = point + [[],-180,180]
        if x in terminals:
            terminalsbyindex.append(terminals.index(x))
    terminalsbyindex.sort()
    i.insert(2,terminalsbyindex)

d = {} #removing fst's if there exists an fst on the same terminals with same or smaller length.
for sub in fst_set:
    k = tuple(sub[2])
    if k not in d or sub[1] < d[k][1]:
        d[k] = sub

fst_set = list(d.values())

jae_set = [[i[0] for i in fst_set],[i[1] for i in fst_set],[i[2] for i in fst_set],[i[3] for i in fst_set]]

output = [test_inputs[0],[point[:2] for point in terminals]]
output.extend(jae_set)
with open('steineroutput.txt', 'w+') as file:
    file.writelines([str(line) + "\n" for line in output])

num_edges = sum(1 for x in fst_set if len(x[2]) == 2)
num_3steiner = sum(1 for x in fst_set if len(x[2]) == 3) 
num_4steiner = sum(1 for x in fst_set if len(x[2]) == 4)

print("The number of terminals was ", test_inputs[0], ". The number of FST's is ", len(fst_set),". That's ", num_edges, " edges, ",num_3steiner, " triples, and ", num_4steiner, " quads.")

fig, ax = plt.subplots()

xs = [point[0] for point in terminals] # this part is for plotting the points 
ys = [point[1] for point in terminals]
plt.scatter(xs,ys)

# for top in jae_set[3]:
    # print(top,"\n")

for tops in jae_set[3]:
    if len(tops) == 2:
        x = [tops[0][0],tops[1][0]]
        y = [tops[0][1],tops[1][1]]
        plt.plot(x,y,'k')
    else:
        for edge in tops:
            x = [edge[0][0],edge[1][0]]
            y = [edge[0][1],edge[1][1]]
            if len(tops) == 3:
                plt.plot(x,y,'g')
            else:
                plt.plot(x,y,'r')

ax.set_xlim([0, 1])
ax.set_ylim([0, 1])
ax.set_aspect('equal')
plt.show()

# x = test_inputs
# y = times
# plt.plot(x, y)
# plt.xlabel('# of terminals')
# plt.ylabel('Time in sec')
# plt.show()