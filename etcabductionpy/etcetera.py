# etcetera.py
# Etcetera Abduction: Probability-ordered logical abduction for kb of definite clauses
# Andrew S. Gordon

import parse
import unify
import abduction
import bisect
import itertools
import time

def etcAbduction(obs, kb, indexed_kb, maxdepth, skolemize = True):
    '''Trying something faster'''
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
    return reduce(
        lambda x, y: x*y,
            [l[1]
            for l in etcs
            if parse.is_etc(l)
            ],
            1.0)

def bestCaseProbability(etcs):
    '''If we were wildly successful at unifing all literals, what would the joint probability be?'''
    predicateSet = set()
    pr = 1.0
    for literal in etcs:
        if literal[0] not in predicateSet:
            predicateSet.add(literal[0])
            pr = pr * literal[1]
    return pr

def nbest(obs, kb, indexed_kb, maxdepth, n, skolemize = True):
    pr2beat = 0.0
    nbest = [] # solutions
    nbestPr = [] # probabilities
    listoflists = [abduction.and_or_leaflists([ob], indexed_kb, maxdepth) for ob in obs]
    for u in itertools.product(*listoflists):
        u = list(itertools.chain.from_iterable(u))

        # check if the solution contains etcetera literals only.
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
