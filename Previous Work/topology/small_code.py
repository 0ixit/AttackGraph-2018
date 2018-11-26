from z3 import *

import time
import random

def flat(unflat):
    flat_dict = []
    for sublist in unflat:
        for item in sublist:
            flat_dict.append(item)
    return flat_dict

def attack_graph():

    t = time.time()

    n_size, unroll, base = 4, 3, 1

    s         = Solver()
    node      = []
    edge_list = []

    node_id     =   []
    node_type   =   []
    node_safe   =   []
    node_domain =   []

    for i in range(unroll+base):
        unflat = [ BitVecs('node_id_%d_%d' % (i, j), 4) for j in range(n_size)]
        node_id.append(flat(unflat))

        unflat = [ BitVecs('node_type_%d_%d' % (i, j), 3) for j in range(n_size)]
        node_type.append(flat(unflat))

        unflat = [ Bools('node_safe_%d_%d' % (i, j)) for j in range(n_size)]
        node_safe.append(flat(unflat))
        
        unflat = [ BitVecs('node_domain_%d_%d' % (i, j), 2) for j in range(n_size)]
        node_domain.append(flat(unflat))

    tuple = z3.Datatype('tuple')
    tuple.declare('tuple',('f1', BitVecSort(4)), ('f2', BitVecSort(3)), ('f3', BoolSort()), ('f4', BitVecSort(2)))
    tuple = tuple.create()

    edge = z3.Datatype('edge')
    edge.declare('edge',('f1', tuple), ('f2', tuple))
    edge = edge.create()
    
    for i in range(unroll+base):
        node.append([tuple.tuple(node_id[i][j], node_type[i][j], node_safe[i][j], node_domain[i][j]) for j in range(n_size)])    


    node[0][0]  = tuple.tuple(0, 0, False, 0)
    node[0][1]  = tuple.tuple(1, 0, True, 0) 
    node[0][2]  = tuple.tuple(2, 0, True, 0)
    node[0][3]  = tuple.tuple(3, 0, True, 0) 
    #node[0][4]  = tuple.tuple(4, 0, True, 2)

    edge_list.append(edge.edge(node[0][0],  node[0][1]))
    edge_list.append(edge.edge(node[0][1],  node[0][2]))
    edge_list.append(edge.edge(node[0][2],  node[0][3]))
    #edge_list.append(edge.edge(node[0][3],  node[0][4]))

    a = z3.K(edge, False)

    for i in range(len(edge_list)):
        a = z3.Store(a, edge_list[i], True)

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

            if(s.check()==sat):
                m = s.model()
                print("i=%d, p=%d, u=%d\n" %(i, p, u))
                print("node[%d][%i] : %s" %(p, 0, m.eval(node[p][0])))
                print("node[%d][%i] : %s" %(p, 1, m.eval(node[p][1])))
                print("node[%d][%i] : %s" %(p, 2, m.eval(node[p][2])))
                print("node[%d][%i] : %s" %(p, 3, m.eval(node[p][3])))
                print()
                print("node[%d][%i] : %s" %(u, 0, m.eval(node[u][0])))
                print("node[%d][%i] : %s" %(u, 1, m.eval(node[u][1])))
                print("node[%d][%i] : %s" %(u, 2, m.eval(node[u][2])))
                print("node[%d][%i] : %s\n" %(u, 3, m.eval(node[u][3])))
                print()

            
        safety = []
        for i in range(n_size):
            safety.append(Implies(tuple.f4(node[c][i]) == 2, tuple.f3(node[c][i]) == True))
        #s.add(*safety)
            
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
                        #print("node[%d][%i] : %s" %(ui, i, m.eval(node[ui][i])))
                    except:
                        pass

attack_graph()
