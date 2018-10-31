"""
index = 0
from z3 import *

# init  -->  set of initial state
# goal  -->  set of final state
# trans -->  set of transition relation

trans = [(1,4), (2,4), (3,4), (4,5), (4,6), (5,7), (5,8), (6,7), (6,8)];

x0, x1 = Consts('x0 x1', BitVecSort(4))

s = Solver()

init = [Or(x0==1, x0==2, x0==3)]
	
s.add(init)
s.add(final)
print(s.check())
print(s.model())


print(x0, x1)
"""
 
from collections import defaultdict 
  
class Graph: 
  
    def __init__(self): 
 
        self.graph = defaultdict(list) 
 

    def addEdge(self,u,v): 
        self.graph[u].append(v)
        # {0: [3], 1: [3], 2: [3], 3: [4, 5], 4: [6, 7], 5: [6, 7], 6: [6], 7: [7]})

    def safeBFS(self, s): 
        visited = [False] * (len(self.graph)) 

        queue = [] 
  
        queue.append(s) 
        visited[s] = True
  
        while queue: 
            s = queue.pop(0) 
            
            for i in goal:
                if i == s:
                    return True

            for i in self.graph[s]:
                if visited[i] == False:
                    queue.append(i)
                    visited[i] = True


                    

g = Graph() 

init = [0,1,2]
goal = [6,7]

g.addEdge(0, 3) 
g.addEdge(1, 3) 
g.addEdge(2, 3) 
g.addEdge(3, 4) 
g.addEdge(3, 5)
g.addEdge(4, 6)
g.addEdge(4, 7)
g.addEdge(5, 6)
g.addEdge(5, 7)
g.addEdge(6, 6)
g.addEdge(7, 7)

for i in init:
    if g.safeBFS(i) == True:
        print("Vulenrable State"+str(i))
    else :
        print("Safe State"+str(i))

