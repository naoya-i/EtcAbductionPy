import mcdb
import cPickle
import abduction
import collections
import parse
import unify

class text_t:
    def __init__(self, dct):
        self.dct = dct

    def __getitem__(self, k):
        return self.dct.get(k)

    def __contains__(self, k):
        return self.dct.has_key(k)

    def get_facts(self):
        return []

    def get_axioms(self):
        return self.dct.values()

class mcdb_t:
    def __init__(self, f):
        self.mcdb = mcdb.read(f)

    def __getitem__(self, k):
        ret = self.mcdb.find(k)

        if None != ret:
            ret = cPickle.loads(ret)
            assert(type(ret) == list)
            return ret

        return []

    def __contains__(self, k):
        return self.mcdb.find(k) != None

    def get_facts(self):
        return cPickle.loads(self.mcdb["__fact__"])

    def get_axioms(self):
        ret = []

        for k in self.mcdb.keys():
            ret += self[k]

        return ret

def obtain_relevant_kb(kb, conj, maxdepth):
    """obtain relevant axioms to conj."""

    # relevant reasoning.
    ret, bkon, queue = set(), set(), []
    etcized          = collections.defaultdict(int)

    # add observations to the queue.
    for ob in conj:
        queue += [(0, tuple(ob))]

    while len(queue) > 0:
        lv, p = queue.pop()

        if (lv, p) in bkon or parse.is_etc(p):
            continue

        bkon.add((lv, p))

        if not parse.is_negated(p):
            etcized[p] += 0

        if lv == maxdepth:
            continue

        # add rule to the result and prepare for next queue.
        for relevant_rule in kb[p[0]]:
            # for first-order literal.
            if not parse.is_propositional(p):

                # instantiate the axiom.
                theta = unify.unify(p, parse.consequent(relevant_rule))

                if theta == None:
                    continue

                relevant_rule = unify.standardize(unify.subst(theta, relevant_rule))

            # collect abducibles. mark `p` as an abducible.
            etcized[p] += 1

            # add to the relevant axioms and continue reasoning.
            ret.add(parse.list2tuple(relevant_rule))

            for lit in parse.antecedent(relevant_rule):
                lit = tuple(lit)

                if not parse.is_etc(lit):
                    queue += [(lv+1, lit)]

    return list(ret), kb.get_facts(), [l for l in etcized if etcized[l] == 0]

def cache_kb(fnout, kbkb, kbfacts):
    mk = mcdb.make(fnout)

    for p, rules in abduction.index_by_consequent_predicate(kbkb).iteritems():
        mk.add(p, cPickle.dumps(rules))

    mk.add("__fact__", cPickle.dumps(kbfacts))
    mk.finish()
