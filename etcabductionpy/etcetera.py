# etcetera.py
# Etcetera Abduction: Probability-ordered logical abduction for kb of definite clauses
# Andrew S. Gordon

import unify
import abduction
import bisect
import itertools

import gurobipy
import math

def etcAbduction(obs, kb, maxdepth, skolemize = True):
    '''Trying something faster'''
    indexed_kb = abduction.index_by_consequent_predicate(kb)
    res = []
    listoflists = [abduction.and_or_leaflists([ob], indexed_kb, maxdepth) for ob in obs]

    for u in itertools.product(*listoflists):
        u = list(itertools.chain.from_iterable(u))
        res.extend(abduction.crunch(u))
    res.sort(key=lambda item: jointProbability(item), reverse=True)
    if skolemize:
        return [unify.skolemize(r) for r in res]
    else:
        return res

def jointProbability(etcs):
    return reduce(lambda x, y: x*y, [l[1] for l in etcs])

def bestCaseProbability(etcs):
    '''If we were wildly successful at unifing all literals, what would the joint probability be?'''
    predicateSet = set()
    pr = 1.0
    for literal in etcs:
        if literal[0] not in predicateSet:
            predicateSet.add(literal[0])
            pr = pr * literal[1]
    return pr

def nbest(obs, kb, maxdepth, n, skolemize = True):
    indexed_kb = abduction.index_by_consequent_predicate(kb)
    pr2beat = 0.0
    nbest = [] # solutions
    nbestPr = [] # probabilities
    listoflists = [abduction.and_or_leaflists([ob], indexed_kb, maxdepth) for ob in obs]
    for u in itertools.product(*listoflists):
        u = list(itertools.chain.from_iterable(u))
        if bestCaseProbability(u) > pr2beat:
            for solution in abduction.crunch(u):
                jpr = jointProbability(solution)
                if jpr > pr2beat:
                    insertAt = bisect.bisect_left(nbestPr, jpr)
                    nbest.insert(insertAt, solution)
                    nbestPr.insert(insertAt, jpr)
                    if len(nbest) > n:
                        nbest.pop(0)
                        nbestPr.pop(0)
                        pr2beat = nbestPr[0] # only if full
    nbest.reverse() # [0] is now highest
    if skolemize:
        return [unify.skolemize(r) for r in nbest]
    else:
        return nbest

def ilpsol(obs, kb, maxdepth, n):
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
        # c_{l1 \land l2 \land ...} <=> x_l1 \land x_l2 \land ...
        for conj in possible_expls:
            gm.addConstr(len(conj)*cvars[_conj2predsid(conj)] == sum([xvars[l[0]] for l in conj]))

        #
        if len(possible_expls) > 0:
            # constraint: p can be concluded iff at least one of its explanations is concluded.
            # x_p <=> c_{Q_1} \lor c_{Q_2} or ...
            gm.addConstr(xvars[predicate] <= sum([cvars[_conj2predsid(conj)] for conj in possible_expls]))
            gm.addConstr(sum([cvars[_conj2predsid(conj)] for conj in possible_expls]) <= len(possible_expls)*xvars[predicate])

            # constraint: explanations are mutually exclusive.
            gm.addConstr(sum([cvars[_conj2predsid(conj)] for conj in possible_expls]) <= 1)

        else:
            # constraint: p can be concluded iff it is assumed.
            # x_p <=> h_p
            gm.addConstr(xvars[predicate] == hvars[predicate])
            assert(predicate.startswith("etc"))

    # observation must be explained.
    gm.addConstr(sum([xvars[l[0]] for l in obs]) >= len(obs))

    # set ILP objective.
    gm.setObjective(sum([math.log(prob) * hvars[predicate] for predicate, prob in etcliterals]), gurobipy.GRB.MAXIMIZE)
    gm.update()
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
