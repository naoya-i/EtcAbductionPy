
import formula
import parse

import networkx as nx

import sys
import bisect
import math
import itertools
import logging

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
            if literal[0] not in self.ikb:
                logging.info("No explanation: %s" % literal)
                continue

            gnid_lit = f._create_node(tuple(literal))
            f.nxg.add_edge(gnid_cnj, gnid_lit)

        open_list += [candidate_t(self.h(f), f)]
        expanded = set([tuple([n[1] for n in f.nxg.nodes()])])

        nc = 0

        while len(open_list) > 0:
            op = open_list.pop()
            expanded.remove(tuple([n[1] for n in op.formula.nxg.nodes()]))

            try:
                for score, f in self.expand(op.formula):
                    if score <= -10000:
                        continue

                    sig = tuple([n[1] for n in f.nxg.nodes()])

                    if sig in expanded:
                        continue

                    bisect.insort_right(open_list, candidate_t(score, f))
                    expanded |= set([sig])

            except SolvedException:
                yield list(set([n[1] for n in op.formula.nxg.nodes() if parse.is_etc(n[1])]))

                if self.graph:
                    op.formula.visualize(sys.stdout)

                nc += 1

                if nc == self.nbest:
                    break

            except NoExpansionException:
                pass

    def expand(self, f):
        expansions = {}
        solved = True

        # search for possibility on expansion.
        for node in f.nxg.nodes_iter():
            predicate = node[1][0]
            depth = len(nx.ancestors(f.nxg, node)) - 1

            if len(f.nxg.successors(node)) > 0:
                continue

            if parse.is_etc(node[1]):
                continue

            # non-etc, leaf node.
            solved = False

            expansions[node] = []

            if predicate in self.ikb:

                # backchain on the literal.
                for rule in self.ikb[predicate]:

                    # do not expand beyond the max depth.
                    if depth == self.maxdepth - 1:
                        if len([l for l in parse.antecedent(rule) if not parse.is_etc(l)]) > 0:
                            continue

                    expansions[node] += [(node, parse.antecedent(rule))]

        if solved:
            raise SolvedException

        products = [x for x in expansions.values() if len(x) > 0]

        if len(products) == 0:
            raise NoExpansionException

        for exp in itertools.product(*products):
            f_new = f.copy()

            for node, expansion in exp:
                for lit in expansion:
                    gnid_lit = f_new._create_node(tuple(lit))
                    f_new.nxg.add_edge(node, gnid_lit)

            yield self.h(f_new), f_new

    def _get_estimated_cost(self, literal, depth, assumed_etc, assumed = [], conj = []):
        predicate = literal[0]

        if parse.is_etc(literal):
            if tuple(literal) in assumed_etc:
                return 0.0 # return best case probability.

            assumed_etc |= set([tuple(literal)])
            return math.log(literal[-1])

        if depth >= self.maxdepth:
            return -10000

        # if predicate in set(assumed):
        #     return -100

        if self.cache.has_key((tuple(conj), predicate, )):
            return self.cache[(tuple(conj), predicate, )]

        ret = -10000 # Meaning zero prob.

        if predicate in self.ikb:

            # backchain on the literal.
            costs = []

            for rule in self.ikb[predicate]:
                local_cost = 0.0

                for lit in parse.antecedent(rule):
                    local_cost += self._get_estimated_cost(lit, depth+1, assumed_etc, assumed + [predicate], (tuple(literal), tuple([tuple(x) for x in parse.antecedent(rule)])))

                costs += [local_cost]

            ret = max(costs)

        self.cache[(tuple(conj), predicate, )] = ret

        return ret

    def h(self, f):
        ret = 0.0
        etc_nodes = []
        assumed_etc = set([])

        # first, scan all leaf etc literals.
        for node in f.nxg.nodes_iter():
            if len(f.nxg.successors(node)) == 0 and parse.is_etc(node[1]):
                assumed_etc |= set([tuple(node[1])])

        for node in f.nxg.nodes_iter():
            if len(f.nxg.successors(node)) > 0:
                continue

            if parse.is_etc(node[1]):
                etc_nodes += [node[1]]
                continue

            depth = len(nx.ancestors(f.nxg, node)) - 1

            ret += self._get_estimated_cost(node[1], depth, assumed_etc)

        ret += sum([math.log(p) for l, p in set(etc_nodes)])

        return ret

class NoExpansionException(Exception):
    pass

class SolvedException(Exception):
    pass

class candidate_t:
    def __init__(self, score, formula):
        self.score, self.formula = score, formula

    def __lt__(self, other):
        return self.score < other.score
