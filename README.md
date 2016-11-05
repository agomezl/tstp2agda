tstp2agda [![Build Status](https://travis-ci.org/agomezl/tstp2agda.svg)](https://travis-ci.org/agomezl/tstp2agda)
====


A proof tool for translating TSTP proofs to [Agda] code.
Only [Metis](http://www.gilith.com/software/metis/) proofs for now.
Tested with Metis 2.3 (release 20160714).


## Installation

```
$ git clone https://github.com/agomezl/tstp2agda.git
$ cd tstp2agda
$ cabal install
```

## Usage

```
Usage: tstp2agda [OPTIONS] FILE

  -h       --help              Prints help message
  -o FILE  --output=FILE       Output to file      (default: STDOUT)
  -p NAME  --proof-name=NAME   Main proof name     (default: proof)
           --version           Show version number

```

## First proof reconstruction

Given a problem in TPTP format like this one

```
$ cd examples/problem
$ cat Basic-1.tptp
fof(a1,axiom,a).
fof(a2,axiom,b).
fof(a3,axiom, (a & b) => z).
fof(a4,conjecture,z).
```

we can get a proof in TSTP format using Metis


```
$ metis --show proof Basic-1.tptp > Basic-1.tstp
$ cat Basic-1.tstp
---------------------------------------------------------------------------
SZS status Theorem for Basic-1.tptp

SZS output start CNFRefutation for Basic-1.tptp
fof(a1, axiom, (a)).

fof(a2, axiom, (b)).

fof(a3, axiom, ((a & b) => z)).

fof(a4, conjecture, (z)).

fof(subgoal_0, plain, (z), inference(strip, [], [a4])).
...
```

We proceed to reconstruct using tstp2agda saving the output into an
Agda file

```
$ tstp2agda Basic-1.tstp > Basic-1.agda
$ cat Basic-1.agda

-- | tstp2agda proof

open import Data.FOL.Shallow
open import Function using (id)

-- 0 more viable options
fun-normalize-0-0 : {z : Set} → ¬ z → ¬ z
fun-normalize-0-0 = id

postulate fun-normalize-0-1 : {a b z : Set} → (a ∧ b → z) → ¬ a ∨ ¬ b ∨ z

-- 0 more viable options
fun-normalize-0-2 : {a : Set} → a → a
fun-normalize-0-2 = id

-- 0 more viable options
fun-normalize-0-3 : {b : Set} → b → b
fun-normalize-0-3 = id

postulate fun-normalize-0-4 : {a b z : Set} → ¬ a ∨ ¬ b ∨ z → a → b → z

postulate fun-normalize-0-5 : {z : Set} → ¬ z → z → ⊥

postulate fun-refute-0-0 :  ⊥ → ⊥

postulate goals : {z : Set} → z → z

proof : {a b z : Set} → a → b → (a ∧ b → z) → z
proof {a}{b}{z} a1 a2 a3 = goals subgoal-0
  where
    fun-negate-0-0 : ¬ z → ⊥
    fun-negate-0-0 negate-0-0 = refute-0-0
      where
        normalize-0-0 = fun-normalize-0-0 negate-0-0
        normalize-0-1 = fun-normalize-0-1 a3
        normalize-0-2 = fun-normalize-0-2 a1
        normalize-0-3 = fun-normalize-0-3 a2
        normalize-0-4 = fun-normalize-0-4 normalize-0-1 normalize-0-2 normalize-0-3
        normalize-0-5 = fun-normalize-0-5 normalize-0-0 normalize-0-4
        refute-0-0 = fun-refute-0-0 normalize-0-5
    subgoal-0 = proofByContradiction fun-negate-0-0

```

If everything is alright, we can type-check the Agda file and that's
all

```
$ agda Basic-1.agda
```

## Links

* [Agda](http://wiki.portal.chalmers.se/agda/pmwiki.php)
* [TSTP](http://www.cs.miami.edu/~tptp/TSTP/)
