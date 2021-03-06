# abduction.py
# Logical abduction for kb of definite clauses
# Andrew S. Gordon

import parse
import unify
import itertools
import collections

def abduction(obs, kb, maxdepth, skolemize = True):
    '''Logical abduction: returns a list of all sets of assumptions that entail the observations given the kb'''
    indexed_kb = index_by_consequent_predicate(kb)
    res = []
    listoflists = [and_or_leaflists([ob], indexed_kb, maxdepth) for ob in obs]
    for u in itertools.product(*listoflists):
        u = list(itertools.chain.from_iterable(u))
        res.extend(crunch(u))
    if skolemize:
        return [unify.skolemize(r) for r in res]
    else:
        return res
        
def index_by_consequent_predicate(kb):
    res = {}
    for dc in kb:
        predicate = parse.consequent(dc)[0]
        if predicate in res:
            res[predicate].append(dc)
        else:
            res[predicate] = [dc]
    return res

def and_or_leaflists(remaining, indexed_kb, depth, antecedents = [], assumptions = []):
    '''Returns list of all entailing sets of leafs in the and-or backchaining tree'''
    if depth == 0 and len(antecedents) > 0: # fail
        return [] # (empty) list of lists
    elif len(remaining) == 0: # done with this level
        if len(antecedents) == 0: # found one
            return [assumptions] # list of lists
        else:
            return and_or_leaflists(antecedents, indexed_kb, depth - 1, [], assumptions)
    else: # more to go on this level
        literal = remaining[0] # first of remaining
        predicate = literal[0]

        if predicate not in indexed_kb:
            return and_or_leaflists(remaining[1:], indexed_kb, depth, antecedents, [literal] + assumptions) # shift literal to assumptions
        else:
            revisions = []
            for rule in indexed_kb[predicate]: # indexed by predicate of literal
                theta = unify.unify(literal, parse.consequent(rule))
                if theta != None:
                    if depth == 0: # no depth for revision
                        return [] # (empty) list of lists
                    revisions.append([unify.subst(theta, remaining[1:]), # new remaining with substitutions
                                      indexed_kb,
                                      depth,
                                      unify.standardize(unify.subst(theta, parse.antecedent(rule))) +
                                      unify.subst(theta, antecedents),  # new antecedents with substitutions
                                      unify.subst(theta, assumptions)]) # new assumptions with substitutions

            return itertools.chain(*[and_or_leaflists(*rev) for rev in revisions]) # list of lists (if any)

def crunch(conjunction): # returns a list of all possible ways to unify conjunction literals
    conjunction = [k for k,v in itertools.groupby(sorted(conjunction))] # remove duplicates
    res = [conjunction] # start with one solution
    pairs = itertools.combinations(conjunction, 2)
    thetas = [theta for theta in [unify.unify(p[0], p[1]) for p in pairs] if theta is not None]
    ps = powerset(thetas)
    for thetaset in ps:
        if len(thetaset) > 0:
            consistent = mergethetas(thetaset)
            if consistent:
                rewrite = [k for k,v in itertools.groupby(sorted(unify.subst(consistent, conjunction)))]
                if rewrite not in res: # expensive!
                    res.append(rewrite)
    return res

def mergethetas(thetaset):
    '''Merge all substitutions into a single dictionary, or None if not consistent'''
    x = []
    y = []
    for theta in thetaset:
        for var in theta:
            x.append(var)
            y.append(theta[var])
    return unify.unify(x,y)

def powerset(iterable):
    "powerset([1,2,3]) --> () (1,) (2,) (3,) (1,2) (1,3) (2,3) (1,2,3)"
    s = list(iterable)
    return itertools.chain.from_iterable(itertools.combinations(s, r) for r in range(len(s)+1))

# To do: First check for universals in observations
# To do: We can handle universals in the observations if we get andorleaflists for
#  sets of observations literals with overlapping variables.
