# etcetera_ilp.py
# Etcetera Abduction: Probability-ordered logical abduction for kb of definite clauses
# Andrew S. Gordon

import unify
import abduction
import bisect
import itertools

import gurobipy
import math

def ilpsol(obs, kb, maxdepth, n, verbose = False):
    indexed_kb = abduction.index_by_consequent_predicate(kb)
    res = []

    gm = gurobipy.Model("etcabduction")

    hvars, xvars, cvars = {}, {}, {}
    etcliterals  = set([])

    #
    # add ILP variables.
    for literal, literal_conj, possible_expls in abduction.comp_deduce_andor_assumptions(obs, indexed_kb, maxdepth):
        predicate = literal[0]

        # vars for hypothesis H.
        if predicate.startswith("etc"):
            etcliterals |= set([(predicate, literal[-1])])

            if not hvars.has_key(predicate):
                hvars[predicate] = gm.addVar(vtype=gurobipy.GRB.BINARY, name="h_"+predicate)

        # vars for logical consequences of H \cup B
        if not xvars.has_key(predicate):
            xvars[predicate] = gm.addVar(vtype=gurobipy.GRB.BINARY, name="x_"+predicate)

        # vars for conjunction.
        for conj in possible_expls:
            predicates = ",".join([l[0] for l in conj])

            if not cvars.has_key(predicates):
                cvars[predicates] = gm.addVar(vtype=gurobipy.GRB.BINARY, name="c_{%s}"%predicates)

    gm.update()

    #
    # add ILP constraints.
    def _conj2predsid(x):
        return ",".join([l[0] for l in x])

    for literal, literal_conj, possible_expls in abduction.comp_deduce_andor_assumptions(obs, indexed_kb, maxdepth):
        predicate = literal[0]

        # constraint: conjunction is true iff all literals are concluded.
        # c_{l1 \land l2 \land ...}=1 <=> x_l1=1 \land x_l2=1 \land ...
        for conj in possible_expls:
            gm.addConstr(len(conj)*cvars[_conj2predsid(conj)] == sum([xvars[l[0]] for l in conj]))

        # encode condition of literal being concluded.
        if len(possible_expls) > 0:
            # constraint: p can be concluded iff at least one of its explanations is concluded.
            # x_p=1 <=> c_{Q_1}=1 \lor c_{Q_2}=1 or ...
            gm.addConstr(xvars[predicate] <= sum([cvars[_conj2predsid(conj)] for conj in possible_expls]))
            gm.addConstr(sum([cvars[_conj2predsid(conj)] for conj in possible_expls]) <= len(possible_expls)*xvars[predicate])

            # constraint: explanations are mutually exclusive.
            gm.addConstr(sum([cvars[_conj2predsid(conj)] for conj in possible_expls]) <= 1)

        else:
            # constraint: p can be concluded iff it is assumed.
            # x_p=1 <=> h_p=1
            gm.addConstr(xvars[predicate] == hvars[predicate])
            assert(predicate.startswith("etc"))

    # constraint: observation must be concluded.
    # for all p \in O, x_p=1.
    gm.addConstr(sum([xvars[l[0]] for l in obs]) >= len(obs))

    # set ILP objective.
    gm.setObjective(sum([math.log(prob) * hvars[predicate] for predicate, prob in etcliterals]), gurobipy.GRB.MAXIMIZE)
    gm.update()

    gm.params.outputFlag = 0

    if verbose:
        gm.params.outputFlag = 1
        gm.write("test.lp")

    # get solutions.
    sols = []

    for i in xrange(n):

        # find the best assignment.
        gm.optimize()

        #
        # add new solution (if any).
        if gm.getAttr(gurobipy.GRB.Attr.SolCount) == 0:
            break

        sols += [[
            [predicate, prob]
            for predicate, prob in etcliterals
            if hvars[predicate].getAttr(gurobipy.GRB.Attr.X) == 1.0
            ]]

        # deny the current sol.
        gm.addConstr(sum([
            hvars[predicate]
            if hvars[predicate].getAttr(gurobipy.GRB.Attr.X) == 1.0 else
            1.0 - hvars[predicate]
            for predicate, prob in etcliterals
            ]) <= len(etcliterals)-1)

    return sols
