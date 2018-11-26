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
    node[10] = tuple.tuple(4, False, 1)
    node[11] = tuple.tuple(4, False, 1)
    node[12] = tuple.tuple(5, True, 2)
    node[13] = tuple.tuple(6, True, 2)
    node[14] = tuple.tuple(3, True, 2)
    node[15] = tuple.tuple(3, True, 2)

    ## creation of routing table

    edge_list = []
    edge_list.append(edge.edge(node[0],  node[4]))
    edge_list.append(edge.edge(node[1],  node[4]))
    edge_list.append(edge.edge(node[2],  node[4]))
    edge_list.append(edge.edge(node[3],  node[4]))
    edge_list.append(edge.edge(node[4],  node[10]))
    edge_list.append(edge.edge(node[10], node[14]))
    edge_list.append(edge.edge(node[5],  node[9]))
    edge_list.append(edge.edge(node[6],  node[9]))
    edge_list.append(edge.edge(node[7],  node[9]))
    edge_list.append(edge.edge(node[8],  node[9]))
    edge_list.append(edge.edge(node[9],  node[11]))
    edge_list.append(edge.edge(node[11],  node[12]))
    edge_list.append(edge.edge(node[12],  node[13]))
    edge_list.append(edge.edge(node[13],  node[15]))

    arr = z3.K(edge, False)

    for i in range(len(edge_list)):

        arr = z3.Store(arr, edge_list[i], True)

    ###################################
    ## @Pre_Last_Stage
    ## The Unrolling
    ###################################
     
    unroll = 1
    
    unroll_list = []

    s = Solver()
    
    x = []
    
    for i in range(10):
        print(i)
        x.append((edge.f1(edge_list[i]) == node[i]))    

    i = Int('i')


    #can't
    ForAll([i], Implies(And(i < 16), node[i] == edge.f1(edge_list[i])))

    s.add(Or(*x))

    # for c in s.assertions():
    #     print(c)

    print(s.check())
    m = s.model()
    print(m.eval(node[i]))

    ###################################
    ## @Last_Stage
    ## The Final Verification
    ###################################
    
    # safety_list = []
    # s = Solver()

    # for c in s.assertions():
    #     print(c)

    # for i in range(0, n_size):
    #     x = Implies(And(tuple.f1(node[i]) == 3, tuple.f3(node[i]) == 2, ), tuple.f2(node[i]) == True)
    #     safety_list.append(x)

    # safety = Not(And(*safety_list))

    # s.add(safety)

    # print(s.check())
    # if(s.check() == sat):
    #     print(s.model())
    
    # t = time.time() - t
    # #print("\ndelay : ",t)

attack_graph()
