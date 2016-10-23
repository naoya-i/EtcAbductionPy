
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
        self.hop = maxdepth-2
        self.cache = {}

        self.num_expanded = 0
        self.num_popped   = 0

    def search(self, conj, level = 0, from_id = 0):
        open_list = []

        # add observation as a start state.
        f = []

        for literal in conj:
            f += [(0, 0, tuple(literal))]

        open_list += [candidate_t(self.estimate_cost(f), f)]
        sols       = []

        # start the search.
        while len(open_list) > 0 and len(sols) < self.nbest:
            op = open_list.pop()
            self.num_popped += 1

            try:
                # expand and add to the priority queue.
                num_expansion = 0
                logging.info("Expanding...")

                for score, f in self.expand(op.formula):
                    if score <= -10000:
                        continue

                    bisect.insort_left(open_list, candidate_t(score, f))
                    num_expansion += 1

                logging.info("Whew... %d expansion." % num_expansion)
                self.num_expanded += num_expansion

                # output the graph.
                if self.graph:
                    op.formula.visualize(sys.stdout)

            except SolvedException:
                # oh, the popped graph is already solved one.
                sol = frozenset([lit for t, lv, lit in op.formula if parse.is_etc(lit)])

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

        # change the estimation strategy.
        self.hop = self.maxdepth+1

        # take a cartesian product of them.
        for exp in itertools.product(*expansions.values()):
            f_new = list(f)

            for node, expansion in exp:
                i, t, lv, node = node

                # mark the node as closed node.
                f_new[i] = (1, lv, node)

                # add expanded literals.
                for lit in expansion:
                    f_new += [(0, lv+1, tuple(lit))]

            yield self.estimate_cost(f_new), f_new

    def estimate_cost(self, f):
        assumed_etc = set()
        fixed_etc   = set()
        estimated_etc_count = collections.defaultdict(int)

        # g(E): sum of all resolved etc literals.
        est_g = 0.0
        open_nodes = []

        for t, lv, node in f:

            # looking for leaf nodes.
            if parse.is_etc(node):
                fixed_etc.add(node)
                estimated_etc_count[node] += 1

            elif t == 0:
                open_nodes += [node]

                for l in self._enum_etcs(node, lv):
                    estimated_etc_count[l] += 1

        est_g += sum([math.log(p) for l, p in fixed_etc])

        # h(E): maximum score among all possible paths!
        est_h = 0.0

        estimated_assumed_etc = set([l for l, c in estimated_etc_count.iteritems() if c >= 2])
        assumed_etc = fixed_etc | estimated_assumed_etc

        for node in open_nodes:
            hf = self._estimate_cost_node(node, lv)
            est_h += hf((assumed_etc, 1.0))

        # i'm still not sure the below tight bound makes sense or not.
        if len(estimated_assumed_etc) > 0:
            lowest_etc = max(estimated_assumed_etc, key=lambda e: e[-1])

            if lowest_etc not in fixed_etc:
                est_h += math.log(lowest_etc[-1])

        # f(E) = g(E) + h(E)
        return est_g + est_h

    def _obtain_all_possible_expansions(self, f):
        expansions = collections.defaultdict(list)
        solved = True

        # search for possibility on expansion.
        for i, node in enumerate(f):
            t, lv, node = node
            predicate = node[0]

            if t != 0 or parse.is_etc(node):
                continue

            # non-etc, leaf node.
            solved = False

            if predicate in self.ikb:

                # backchain on the literal.
                for rule in self.ikb[predicate]:

                    # do not expand beyond the max depth.
                    if lv == self.maxdepth - 1:
                        if len([l for l in parse.antecedent(rule) if not parse.is_etc(l)]) > 0:
                            continue

                    expansions[i] += [((i, t, lv, node), parse.antecedent(rule))]

        # already solved?
        if solved:
            raise SolvedException

        # no expansion?
        if len(expansions) == 0:
            raise NoExpansionException

        return expansions

    def _enum_etcs(self, literal, depth):
        literal   = tuple(literal)
        predicate = literal[0]

        if parse.is_etc(literal):
            return [literal]

        else:

            if not self.cache.has_key((1008, literal, depth)):
                # try backchaining on the literal.
                literals = []

                if depth < self.maxdepth and predicate in self.ikb:
                    for rule in self.ikb[predicate]:
                        for lit in parse.antecedent(rule):
                            literals.extend(self._enum_etcs(lit, depth+1))

                self.cache[(1008, literal, depth)] = literals

            return self.cache[(1008, literal, depth)]


    def _estimate_cost_node(self, literal, depth, hop = 0):
        predicate = literal[0]

        ret = _hf_const(-10000) # Meaning zero prob.

        if self.cache.has_key((predicate, depth, )):
            return self.cache[(predicate, depth, )]

        if hop == self.hop:
            return _hf_const(0)

        if parse.is_etc(literal):
            ret = _hf_var(lambda m: math.log(literal[-1]) if tuple(literal) not in m[0] else math.log(m[1]))

        else:

            # try backchaining on the literal.
            if depth < self.maxdepth and predicate in self.ikb:
                costs = []

                for rule in self.ikb[predicate]:
                    local_cost = []

                    for lit in parse.antecedent(rule):
                        local_cost += [self._estimate_cost_node(lit, depth+1, hop+1)]

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
