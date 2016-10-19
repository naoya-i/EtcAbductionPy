
import formula
import parse

import networkx as nx

import sys
import bisect
import math
import itertools
import logging
import collections

class aostar_searcher_t():
    def __init__(self, ikb, maxdepth, nbest, graph):
        self.ikb = ikb
        self.maxdepth = maxdepth
        self.nbest = nbest
        self.graph = graph
        self.cache = {}

    def search(self, conj, level = 0, from_id = 0):
        open_list = []

        f = formula.formula_t()
        gnid_cnj = f._create_node("^")

        for literal in conj:
            gnid_lit = f._create_node(tuple(literal))
            f.nxg.add_edge(gnid_cnj, gnid_lit)

        open_list += [candidate_t(self.estimate_cost(f), f)]
        sols       = []

        while len(open_list) > 0 and len(sols) < self.nbest:
            op = open_list.pop()

            try:
                for score, f in self.expand(op.formula):
                    if score <= -10000:
                        continue

                    bisect.insort_left(open_list, candidate_t(score, f))

            except SolvedException:
                sol = frozenset([n[1] for n in op.formula.nxg.nodes() if parse.is_etc(n[1])])

                if sol in set(sols):
                    continue

                sols += [sol]

                yield list(sol)

                if self.graph:
                    op.formula.visualize(sys.stdout)

            except NoExpansionException:
                pass

    def expand(self, f):
        expansions = collections.defaultdict(list)
        solved = True

        # search for possibility on expansion.
        for node in f.nxg.nodes_iter():
            predicate = node[1][0]

            if len(f.nxg.successors(node)) > 0 or parse.is_etc(node[1]):
                continue

            # non-etc, leaf node.
            solved = False

            if predicate in self.ikb:

                # backchain on the literal.
                for rule in self.ikb[predicate]:

                    # do not expand beyond the max depth.
                    if f.levels[node] == self.maxdepth - 1:
                        if len([l for l in parse.antecedent(rule) if not parse.is_etc(l)]) > 0:
                            continue

                    expansions[node] += [(node, parse.antecedent(rule))]

        if solved:
            raise SolvedException

        if len(expansions) == 0:
            raise NoExpansionException

        for exp in itertools.product(*expansions.values()):
            f_new = f.copy()

            for node, expansion in exp:
                for lit in expansion:
                    gnid_lit = f_new._create_node(tuple(lit), f.levels[node]+1)
                    f_new.nxg.add_edge(node, gnid_lit)

            yield self.estimate_cost(f_new), f_new

    def _estimate_cost_node(self, literal, depth):
        predicate = literal[0]

        ret = (tuple(literal), -10000) # Meaning zero prob.

        if self.cache.has_key((predicate, depth, )):
            return self.cache[(predicate, depth, )]

        if parse.is_etc(literal):
            ret = (tuple(literal), math.log(literal[-1]))

        else:

            # try backchaining on the literal.
            if depth < self.maxdepth and predicate in self.ikb:
                costs = [0] # operator "OR"

                for rule in self.ikb[predicate]:
                    local_cost = [1] # operator "AND"

                    for lit in parse.antecedent(rule):
                        local_cost += [self._estimate_cost_node(lit, depth+1)]

                    # reduction.
                    if len(local_cost) == 2:
                        local_cost = local_cost[1]

                    costs += [local_cost]

                # reduction.
                if len(costs) == 2:
                    costs = costs[1]

                ret = costs

        self.cache[(predicate, depth, )] = ret

        return ret

    def estimate_cost(self, f):
        assumed_etc = set()

        # g(E): sum of all resolved etc literals.
        est_g = 0

        for node in f.nxg.nodes_iter():
            if len(f.nxg.successors(node)) == 0 and parse.is_etc(node[1]):
                assumed_etc.add(tuple(node[1]))

        est_g += sum([math.log(p) for l, p in assumed_etc])

        # h(E): maximum score among all possible paths!
        est_h = 0.0

        for node in f.nxg.nodes_iter():
            if len(f.nxg.successors(node)) > 0 or parse.is_etc(node[1]):
                continue

            hf = heuristic_function_t(self._estimate_cost_node(node[1], f.levels[node]), assumed_etc)

            est_h += hf.reduce()
            assumed_etc.update(hf.enumetc())

        return est_g + est_h

class candidate_t:
    def __init__(self, score, formula):
        self.score, self.formula = score, formula

    def __lt__(self, other):
        return self.score < other.score

class heuristic_function_t:
    def __init__(self, func, assumed_etc):
        self.func = func
        self.assumed_etc = assumed_etc

    def reduce(self, x = None):
        if None == x:
            x = self.func

        if isinstance(x, tuple):
            return 0.0 if x[0] in self.assumed_etc else x[1]
        elif x[0] == 0:
            return max([self.reduce(y) for y in x[1:]])
        elif x[0] == 1:
            return sum([self.reduce(y) for y in x[1:]])

    def enumetc(self, lst = None):
        if None == lst:
            lst = self.func

        if isinstance(lst, tuple):
            yield lst
        else:
            for x in lst[1:]:
                if isinstance(x, tuple):
                    if parse.is_etc(x[0]):
                        yield x[0]
                else:
                    for y in self.enumetc(x):
                        yield y

class NoExpansionException(Exception): pass
class SolvedException(Exception):      pass
