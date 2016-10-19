
import formula
import parse

import networkx as nx

import sys
import bisect
import math
import itertools
import logging
import collections

class astar_searcher_t():
    def __init__(self, ikb, maxdepth, nbest, graph):
        self.ikb = ikb
        self.maxdepth = maxdepth
        self.nbest = nbest
        self.graph = graph
        self.cache = {}

        self.num_expanded = 0

    def search(self, conj, level = 0, from_id = 0):
        open_list = []

        # add observation as a start state.
        f = formula.formula_t()
        gnid_cnj = f._create_node("^")

        for literal in conj:
            gnid_lit = f._create_node(tuple(literal))
            f.nxg.add_edge(gnid_cnj, gnid_lit)

        open_list += [candidate_t(self.estimate_cost(f), f)]
        sols       = []

        # start the search.
        while len(open_list) > 0 and len(sols) < self.nbest:
            op = open_list.pop()

            try:
                # expand and add to the priority queue.
                for score, f in self.expand(op.formula):
                    if score <= -10000:
                        continue

                    bisect.insort_left(open_list, candidate_t(score, f))
                    self.num_expanded += 1

            except SolvedException:
                # oh, the popped graph is already solved one.
                sol = frozenset([n[1] for n in op.formula.nxg.nodes() if parse.is_etc(n[1])])

                # to avoid redundant output.
                if sol in set(sols):
                    continue

                yield list(sol)
                sols += [sol]

                # output the graph.
                if self.graph:
                    op.formula.visualize(sys.stdout)

            except NoExpansionException:
                pass

    def expand(self, f):
        expansions = self._obtain_all_possible_expansions(f)

        # take a cartesian product of them.
        for exp in itertools.product(*expansions.values()):
            f_new = f.copy()

            for node, expansion in exp:
                for lit in expansion:
                    gnid_lit = f_new._create_node(tuple(lit), f.levels[node]+1)
                    f_new.nxg.add_edge(node, gnid_lit)

            yield self.estimate_cost(f_new), f_new

    def estimate_cost(self, f):
        assumed_etc = set()

        # g(E): sum of all resolved etc literals.
        est_g = 0.0

        for node in f.nxg.nodes_iter():
            if len(f.nxg.successors(node)) == 0 and parse.is_etc(node[1]):
                assumed_etc.add(tuple(node[1]))

        est_g += sum([math.log(p) for l, p in assumed_etc])

        # h(E): maximum score among all possible paths!
        est_h = 0.0

        for node in f.nxg.nodes_iter():
            if len(f.nxg.successors(node)) > 0 or parse.is_etc(node[1]):
                continue

            hf = self._estimate_cost_node(node[1], f.levels[node])

            est_h += hf(assumed_etc) # hf.reduce()
            #assumed_etc.update(hf.enumetc())

        # f(E) = g(E) + h(E)
        return est_g + est_h

    def _obtain_all_possible_expansions(self, f):
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

        # already solved?
        if solved:
            raise SolvedException

        # no expansion?
        if len(expansions) == 0:
            raise NoExpansionException

        return expansions

    def _estimate_cost_node(self, literal, depth):
        predicate = literal[0]

        ret = _hf_const(-10000) # Meaning zero prob.

        if self.cache.has_key((predicate, depth, )):
            return self.cache[(predicate, depth, )]

        if parse.is_etc(literal):
            ret = _hf_var(lambda m: math.log(literal[-1]) if tuple(literal) not in m else 0.0)

        else:

            # try backchaining on the literal.
            if depth < self.maxdepth and predicate in self.ikb:
                costs = []

                for rule in self.ikb[predicate]:
                    local_cost = []

                    for lit in parse.antecedent(rule):
                        local_cost += [self._estimate_cost_node(lit, depth+1)]

                    # lambdaize.
                    if len(local_cost) > 1:
                        local_cost = _hf_latesum(local_cost)

                    else:
                        local_cost = _hf_var(local_cost[0])

                    costs += [local_cost]

                # lambdaize.
                if len(costs) > 1:
                    costs = _hf_latemax(costs)

                else:
                    costs = _hf_var(costs[0])

                ret = costs

        self.cache[(predicate, depth, )] = ret

        return ret

class candidate_t:
    def __init__(self, score, formula):
        self.score, self.formula = score, formula

    def __lt__(self, other):
        return self.score < other.score

# function object for constructing heuristic function.
def _hf_latesum(ar):
    return lambda m: sum([c(m) for c in ar])

def _hf_latemax(ar):
    return lambda m: max([c(m) for c in ar])

def _hf_var(c):
    return lambda m: c(m)

def _hf_const(c):
    return lambda m: c

class NoExpansionException(Exception): pass
class SolvedException(Exception):      pass
