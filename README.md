# EtcAbductionPy

## An implementation of Etcetera Abduction in Python

This software is a reference implementation of Etcetera Abduction. Given a knowledge base of first-order definite clauses and a set of observables, this software identifies the most probable set of assumptions that logically entails the observations, assuming the conditional independence of each assumption.

For more information, see the following:

* Gordon, Andrew S. (2016) Commonsense Interpretation of Triangle Behavior. In Proceedings of the Thirtieth AAAI Conference on Artificial Intelligence (AAAI-16), February 12-17, 2016, Phoenix, Arizona.


# Short memo on updates from the original version

This is a forked project from Andrew Gordon's EtcAbductionPy (https://github.com/asgordon/EtcAbductionPy).


## Requirements

The forked project depends on the following external libraries:

- networkx (http://networkx.readthedocs.io/en/stable/install.html)
    - If you are using `pip`, just type `pip install networkx`
- mcdb (https://github.com/gstrauss/mcdb)
    - Clone the repository and `make`
    - Go to `contrib/python-mcdb` and then `python setup.py install`
- Gurobi optimizer (above 7.0, https://www.gurobi.com/) + Python binding
    - General installation guide:
        - https://www.gurobi.com/downloads/download-center
    - Python binding installation guide:
        - https://www.gurobi.com/documentation/7.0/quickstart_mac/the_gurobi_python_interfac.html


## Efficient S-expression parsing

The use of collections.deque makes S-expression parsing much faster.


## Knowledge base caching

For large knowledge base. This function requires python-mcdb (https://github.com/gstrauss/mcdb).

* `--kbcache [FILE]` or `-kc [FILE]`: create cache of knowledge base on FILE.
* `--kbmcdb [FILE]` or `-km [FILE]`: use cached knowledge base from FILE.

Example:

    # Create a cache.
    python etcabductionpy -k kb.lisp -kc kb.lisp.mcdb

    # Use the cache for inference.
    python etcabductionpy -km kb.lisp.mcdb ...


## Integer Linear Programming-based inference

The main option is:

* `--ilp` or `-l`: Use ILP solver (gurobi) to search the (n-)best solution(s).

For advanced use:

* `--ilp-show-nonetc` or `-lnonetc`: Output non-etc literals.
* `--ilp-verbose` or `-lv`: Output an ILP solver log.
* `--ilp-no-relreason` or `-lnorel`: Do not perform relevant reasoning.
* `--ilp-use-cnf` or `-lcnf`: Use CNF for clark completion.
* `--ilp-no-transitivity` or `-lnotrans`: Do not enforce equality transitivitys.
* `--ilp-lazy-transitivity` or `-llazytrans`: Use lazy constraints for equality transitivity.
