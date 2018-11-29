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
##          2 : inside (critical)
##  }
##
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

    # no of node in network 6
    # unroll step 3

    n_size, unroll, base = 6, 3, 1 
    s         = Solver()
    node      = []
    edge_list = []

    node_id     =   []
    node_type   =   []
    node_safe   =   []
    node_domain =   []

    # creation of z3 variable

    for i in range(unroll+base):
        unflat = [ BitVecs('node_id_%d_%d' % (i, j), 4) for j in range(n_size)]
        node_id.append(flat(unflat))

        unflat = [ BitVecs('node_type_%d_%d' % (i, j), 3) for j in range(n_size)]
        node_type.append(flat(unflat))

        unflat = [ Bools('node_safe_%d_%d' % (i, j)) for j in range(n_size)]
        node_safe.append(flat(unflat))
        
        unflat = [ BitVecs('node_domain_%d_%d' % (i, j), 2) for j in range(n_size)]
        node_domain.append(flat(unflat))

    # creation of z3 datatype

    tuple = z3.Datatype('tuple')
    tuple.declare('tuple',('f1', BitVecSort(4)), ('f2', BitVecSort(3)), ('f3', BoolSort()), ('f4', BitVecSort(2)))
    tuple = tuple.create()

    edge = z3.Datatype('edge')
    edge.declare('edge',('f1', tuple), ('f2', tuple))
    edge = edge.create()
    
    # bmc variable creation

    for i in range(unroll+base):
        node.append([tuple.tuple(node_id[i][j], node_type[i][j], node_safe[i][j], node_domain[i][j]) for j in range(n_size)])    

    # network topology

    node[0][0]  = tuple.tuple(0, 0, False, 0)
    node[0][1]  = tuple.tuple(1, 0, True, 0)
    node[0][2]  = tuple.tuple(2, 0, True, 0)
    node[0][3]  = tuple.tuple(3, 0, True, 0)
    node[0][4]  = tuple.tuple(4, 0, True, 0)
    node[0][5]  = tuple.tuple(5, 0, True, 2)
    

    # creation of routing table

    edge_list = []
    edge_list.append(edge.edge(node[0][0],  node[0][1]))
    edge_list.append(edge.edge(node[0][1],  node[0][2]))
    edge_list.append(edge.edge(node[0][2],  node[0][3]))
    edge_list.append(edge.edge(node[0][1],  node[0][4]))
    edge_list.append(edge.edge(node[0][4],  node[0][5]))
    
    a = z3.K(edge, False)

    for i in range(len(edge_list)):
        a = z3.Store(a, edge_list[i], True)

    # bounded model checking 

    for u in range(1, unroll+base):
        c = u 
        p = u - 1
        equal = []
        for i in range(n_size):
            equal_pr1 = And( tuple.f1(node[c][i]) == tuple.f1(node[p][i])) 
            equal_pr2 = And( tuple.f2(node[c][i]) == tuple.f2(node[p][i]))
            equal_pr4 = And( tuple.f4(node[c][i]) == tuple.f4(node[p][i]))
            equal.extend([equal_pr1, equal_pr2, equal_pr4])
        s.add(*equal)

        for i in range(n_size):
            infected_neighbour = []
            for j in range(n_size): 
                is_edge_exist         =  (Select(a, edge.edge(node[0][j], node[0][i])) == True)
                is_prev_node_unsafe   =  (tuple.f3(node[p][j]) == False)
                make_change           =  (tuple.f3(node[u][i]) == False)

                make_no_change        =  (tuple.f3(node[u][i]) == tuple.f3(node[p][i]))
                
                infection             =  If(And(is_edge_exist, is_prev_node_unsafe), True, False)

                infected_neighbour.append(infection)
            
            s.add(If(Or(*infected_neighbour) == True, make_change, make_no_change))

        
        # safety property    

        safety = []
        for i in range(n_size):
            safety.append(And(tuple.f4(node[c][i]) == 2, tuple.f3(node[c][i]) == False))
        
        s.push()
        s.add(Or(*safety))
        
        # attack graph generation

        x = s.check()
        print("\nunroll : ", u)
        print(x)
        if(x==sat):
            m = s.model()
            for ui in range(u+base):
                print()
                for i in range(n_size):
                    try:
                        pass
                        print("node[%d][%i] : %s" %(ui, i, m.eval(node[ui][i])))
                    except:
                        pass

        s.pop()

        print("\nTime required to run : " + str(round(time.time()-t, 2))+" sec")

attack_graph()
