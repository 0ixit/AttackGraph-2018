from z3 import *
import time
import random

#####################################
#####################################
##
##  @configuration
##
##  node in network = 16 // could be dynamic 
##  node_type :: {
##          0 : pc         
##          1 : laptop
##          2 : mobile
##          3 : server
##          4 : router
##          5 : firewall
##          6 : ids
##          7 : unknown 
##  }
##  
##  node_safe :: {
##          True  : safe
##          False : unsafe
##  }
##  
##  node_domain :: {
##          0 : outside
##          1 : internet
##          2 : inside
##  }
##
##    @configuration_in_depth
##   
##     outside        | internet || Inside
##               
##    0  --> 4  4 --> | 4 -----> || 3
##    1  --> 4        |          ||
##    2  --> 4        |          ||
##    3  --> 4        |          ||
##
##    0  --> 4  4 --> | 4 -----> || 5 --> 6--> 3
##    1  --> 4        |          ||  
##    2  --> 4        |          ||
##    3  --> 4        |          ||
##
#####################################
#####################################


def flat(unflat):
    flat_dict = []
    for sublist in unflat:
        for item in sublist:
            flat_dict.append(item)
    return flat_dict


def attack_graph():

    t = time.time()

    n_size = 16 # network size (could be extend to dynamic) 


    ###################################
    ## @Init_Stage
    ## The Data Structure
    ###################################    


    # node_type = enum { pc, laptop, mobile, server, router, firewall, ids} # 0-7

    unflat = [ BitVecs('node_type_%d' % (i), 3) for i in range(n_size)]
    node_type = flat(unflat)

    # node_safe = enum { safe, unsafe} # 0-1

    unflat = [ Bools('node_safe_%d' % (i)) for i in range(n_size)]
    node_safe = flat(unflat)
    
    # node_domain = { inside, outside, internet} # 0-3

    unflat = [ BitVecs('node_domain_%d' % (i), 2) for i in range(n_size)]
    node_domain = flat(unflat)
    
    # tuple creation

    tuple = z3.Datatype('tuple')
    tuple.declare('tuple',('f1', BitVecSort(3)), ('f2', BoolSort()), ('f3', BitVecSort(2)))
    tuple = tuple.create()

    # creation of node

    node = [tuple.tuple(node_type[i], node_safe[i], node_domain[i]) for i in range(n_size)]
    # print(node) # issue 1 :: i want name of element of node to be in node1, node2, node3 ....

    edge = z3.Datatype('edge')
    edge.declare('edge',('f1', tuple), ('f2', tuple))
    edge = edge.create()
  
    ###################################
    ## @Middle_Stage
    ## The Network Model
    ###################################    


    node[0]  = tuple.tuple(0, False, 0)
    node[1]  = tuple.tuple(1, False, 0)
    node[2]  = tuple.tuple(2, False, 0)
    node[3]  = tuple.tuple(2, False, 0)
    node[4]  = tuple.tuple(4, False, 0)
    node[5]  = tuple.tuple(0, False, 0)
    node[6]  = tuple.tuple(1, False, 0)
    node[7]  = tuple.tuple(2, False, 0)
    node[8]  = tuple.tuple(2, False, 0)
    node[9]  = tuple.tuple(4, False, 0)
    node[10] = tuple.tuple(4, True, 1)
    node[11] = tuple.tuple(4, True, 1)
    node[12] = tuple.tuple(5, True, 2)
    node[13] = tuple.tuple(6, True, 2)
    node[14] = tuple.tuple(3, True, 2)
    node[15] = tuple.tuple(3, True, 2)

    # # creation of routing table

    edge1  = edge.edge(node[0], node[4])
    edge2  = edge.edge(node[1], node[4])
    edge3  = edge.edge(node[2], node[4])
    edge4  = edge.edge(node[3], node[4])
    edge5  = edge.edge(node[4], node[10])
    
    arr = z3.K(edge, False)
    arr = z3.Store(arr, edge1, True)
    arr = z3.Store(arr, edge2, True)
    arr = z3.Store(arr, edge3, True)
    arr = z3.Store(arr, edge4, True)
    arr = z3.Store(arr, edge5, True)

    ###################################
    ## @Pre_Last_Stage
    ## The Unrolling
    ###################################
     
    unroll = 5
    x = random.randrange(0,16)
    for i in range(unroll):
        print(x)


    ###################################
    ## @Last_Stage
    ## The Final Verification
    ###################################
    
    safety_list = []

    s = Solver()

    for i in range(0, n_size):
        x = Implies(And(tuple.f1(node[i]) == 3, tuple.f3(node[i]) == 2, ), tuple.f2(node[i]) == True)
        safety_list.append(x)

    safety = Not(And(*safety_list))

    s.add(safety)

    print(s.check())
    if(s.check() == sat):
        print(s.model())
    
    t = time.time() - t
    #print("\ndelay : ",t)

attack_graph()
