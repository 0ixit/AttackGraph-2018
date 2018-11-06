from z3 import *

def init(state):

    f1a, f1b, f2a, f2b = state[0], state[1], state[2], state[3]

    Init1 = And(f1a == f2a, f1b == f2b)       # f1 == f2
    Init2 = And(f1a <= f1b, f2a <= f2b)       # a <= b
    Init3 = And(f1a >= 0, f2a >= 0)           # a >= 0
    Init4 = And(f1b > 0, f2b > 0)             # b > 0

    Init = []
    Init.extend([Init1, Init2, Init3, Init4])

    return (Init)

def invariant_psi(state):

    f1a, f1b, f2a, f2b = state[0], state[1], state[2], state[3]

    invariant = And(f1a == f2a, f1b == f2b)  # f1 = f2
    return invariant

def property_m(state):

    f1a, f1b, f2a, f2b = state[0], state[1], state[2], state[3]

    invariant = And(f1b == f2b) # f1.b = f2.b
    return invariant

def transition(state_s, state_sp):

    f1a_s, f1b_s, f2a_s, f2b_s = state_s[0], state_s[1], state_s[2], state_s[3]
    f1a_sp, f1b_sp, f2a_sp, f2b_sp = state_sp[0], state_sp[1], state_sp[2], state_sp[3]

    # f.a' = f.b and f.b' = f.a + f.b, for both f1 & f2 

    transition_r = And(f1a_sp == f1b_s, f1b_sp == f1a_s + f1b_s, f2a_sp == f2b_s, f2b_sp == f2a_s + f2b_s) 

    return transition_r

def main():
    
    #### Variable declareation

    s = Solver()
    f1a_s, f1b_s, f2a_s, f2b_s     = Int("f1a_s"), Int("f1b_s"), Int("f2a_s"), Int("f2b_s")     # state S
    f1a_sp, f1b_sp, f2a_sp, f2b_sp = Int("f1a_sp"), Int("f1b_sp"), Int("f2a_sp"), Int("f2b_sp") # state SP

    ## list_variables

    state_s   = [f1a_s, f1b_s, f2a_s, f2b_s]      # state S
    state_sp  = [f1a_sp, f1b_sp, f2a_sp, f2b_sp]  # state SP
    
    ####

     
    #### Constrain Creations   

    Init   = init(state_s)                              # Init(S)

    Psi_S  =  invariant_psi(state_s)                    # Psi(S)
    
    Psi_SP = invariant_psi(state_sp)                    # Psi(SP)

    R_S_SP = transition(state_s, state_sp)              # R(S, SP) 

    P_S = property_m(state_s)                           # P(S)

    #### Constraint add to Solver

    s.push()
    s.add(Not(Implies(And(*Init), Psi_S)))           # Init(S) --> Psi(S)
    r = s.check()
    assert r == unsat
    s.pop()

    s.push()
    s.add(Not(Implies(And(Psi_S, R_S_SP), Psi_SP)))  # (Psi(S) && R(S, SP)) --> Psi(SP)
    r = s.check()
    assert r == unsat
    s.pop()

    s.push()
    s.add(Not(Implies(Psi_S, P_S)))                  #  Psi(S) -- P(S)
    r = s.check()
    assert r == unsat
    s.pop()

    """
    // to print assertions

    for c in s.assertions():
        print(c)    
    """

    print(s.check())
 
    if (s.check()) == sat:
        p = s.model()
        print(p)
    else:
        print("Induction proof holds :)")
        
        """
        // can be used to print model value in some manual order 

        print("f1a_s0 : " + str(p.evaluate(f1a_s0)) + \
         ", f1b_s0 : " + str(p.evaluate(f1b_s0)) + \
         ", f2a_s0 : " + str(p.evaluate(f2a_s0)) + \
         ", f2b_s0 : " + str(p.evaluate(f2b_s0))\
         )

        """
 
if __name__ == '__main__':
    main()

