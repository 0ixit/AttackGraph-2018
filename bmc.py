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
        print(graph[u]) 
  
    def BFS(self, s): 
  
        # Mark all the vertices as not visited 
        visited = [False] * (len(self.graph)) 

        # Create a queue for BFS 
        queue = [] 
  
        # Mark the source node as  
        # visited and enqueue it 
        queue.append(s) 
        visited[s] = True
  
        while queue: 
  
            # Dequeue a vertex from  
            # queue and print it 
            s = queue.pop(0) 
            print (s, end = " ") 
  
            # Get all adjacent vertices of the 
            # dequeued vertex s. If a adjacent 
            # has not been visited, then mark it 
            # visited and enqueue it 
            print(self.graph[s]) 
            for i in self.graph[s]: 
                if visited[i] == False: 
                    queue.append(i) 
                    visited[i] = True

g = Graph() 

g.addEdge(0, 1) 
g.addEdge(0, 2) 
g.addEdge(1, 2) 
g.addEdge(2, 0) 
g.addEdge(2, 3) 
g.addEdge(3, 3) 

g.BFS(2) 
