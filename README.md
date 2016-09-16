# tstp2agda [![Build Status](https://travis-ci.org/agomezl/tstp2agda.svg)](https://travis-ci.org/agomezl/tstp2agda)

A proof tool that translate TSTP proofs to Agda code.

## Installation

```bash
$ git clone https://github.com/agomezl/tstp2agda.git
$ cd tstp2agda
$ cabal install
```

## Usage

```
Usage: tstp2agda [OPTIONS]
  -f File  --file=File, --File=File  TSTP input file     (def: STDIN)
  -o File  --output=File             output to file      (def: STDOUT)
  -p Name  --proof-name=Name         main proof name     (def: proof)
  -m Name  --module-name=Name        module name         (def: Main)
  -h, -?   --help                    prints help message
```
## Inside the code

### How it works `Main.hs`

Given a problem in TPTP format like this one

```Bash
  $ cat problem.tstp
  fof(a1,axiom,a).
  fof(a2,conjecture,a).
```
We can get a proof  in TSTP format using the ATP [Metis](http://www.gilith.com/software/metis/)

```Bash
   $ cat proof.tstp
   -------------------------------------------------------------------------
   SZS status Theorem for examples/problem/Test-1.tstp
   SZS output start CNFRefutation for examples/problem/Test-1.tstp
   fof(a1, axiom, (a)).
   fof(a2, conjecture, (a)).
   fof(subgoal_0, plain, (a), inference(strip, [], [a2])).
   fof(negate_0_0, plain, (~ a), inference(negate, [], [subgoal_0])).
   fof(normalize_0_0, plain, (~ a),
       inference(canonicalize, [], [negate_0_0])).
   fof(normalize_0_1, plain, (a), inference(canonicalize, [], [a1])).
   fof(normalize_0_2, plain, ($false),
       inference(simplify, [], [normalize_0_0, normalize_0_1])).
   cnf(refute_0_0, plain, ($false),
       inference(canonicalize, [], [normalize_0_2])).
   SZS output end CNFRefutation for examples/problem/Test-1.tstp
```

Then, we create some data structures to store all information from the proof.

```Haskell
  main ∷ IO ()
  main = do
   -- read the file
   formulas ← 'parseFile' "proof.tstp"
   -- create a map
   proofmap ← 'buildProofMap' formulas
   -- get subgoals,refutes,axioms, and the conjecture
   let subgoals    = 'getSubGoals' formulas
   let refutes     = 'getRefutes' formulas
   let axioms      = 'getAxioms' formulas
   let (Just conj) = 'getConjeture' formulas
   -- build a 'proofTree' for each subgoal (using his associated refute)
   let prooftree = 'map' ('buildProofTree' proofmap) refutes
```
And the reconstruction process takes place:

``
 -- PREAMBLE: module definitions and imports
 'printPreamble' \"BaseProof\"
 -- STEP 1: Print auxiliary functions
 'printAuxSignatures' proofmap prooftree
 -- STEP 2: Subgoal handling
 'printSubGoals' subgoals conj "goals"
 -- STEP 3: Print main function signature
 'printProofBody' axioms conj "proof" subgoals "goals"
 -- STEP 4: Print all the step of the proof as local definitions
 'mapM_' ('printProofWhere' proofmap  prooftree
```

And `tstp2agda` outputs a Agda code based on the original proof.

```Agda
$ cat BaseProof.agda
module BaseProof where
open import Data.FOL.Shallow
postulate fun-normalize-0-0 : { a : Set} → ¬ a → ¬ a
postulate fun-normalize-0-1 : { a : Set} → a → a
postulate fun-normalize-0-2 : { a : Set} → ¬ a → a → ⊥
postulate fun-refute-0-0 :  ⊥ → ⊥
postulate goals : { a : Set} → a → a
proof : { a : Set} → a → a
proof {a} a1 = goals subgoal-0
 where
   fun-negate-0-0 : ¬ a → ⊥
   fun-negate-0-0 negate-0-0 = refute-0-0
     where
       normalize-0-0 = fun-normalize-0-0 negate-0-0
       normalize-0-1 = fun-normalize-0-1 a1
       normalize-0-2 = fun-normalize-0-2 normalize-0-0 normalize-0-1
       refute-0-0 = fun-refute-0-0 normalize-0-2
     subgoal-0 = proofByContradiction fun-negate-0-0
```

## Links

* [Agda wiki](http://wiki.portal.chalmers.se/agda/pmwiki.php)
* [TSTP](http://www.cs.miami.edu/~tptp/TSTP/)
