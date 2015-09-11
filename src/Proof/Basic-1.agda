module Proof.Basic-1 where

open import Data.FOL.Base
open import Function using (id)

-- example/proof/Basic-1.tstp
-- fof(a1, axiom, (a)).
-- fof(a2, axiom, (b)).
-- fof(a3, axiom, ((a & b) => z)).
-- fof(a4, conjecture, (z)).
-- fof(subgoal_0, plain, (z),
--     inference(strip, [], [a4])).
-- fof(negate_0_0, plain, (~ z),
--     inference(negate, [], [subgoal_0])).
-- fof(normalize_0_0, plain, (~ z),
--     inference(canonicalize, [], [negate_0_0])).
-- fof(normalize_0_1, plain, (~ a | ~ b | z),
--     inference(canonicalize, [], [a3])).
-- fof(normalize_0_2, plain, (a),
--     inference(canonicalize, [], [a1])).
-- fof(normalize_0_3, plain, (b),
--     inference(canonicalize, [], [a2])).
-- fof(normalize_0_4, plain, (z),
--     inference(simplify, [],[normalize_0_1, normalize_0_2, normalize_0_3])).
-- fof(normalize_0_5, plain, ($false),
--     inference(simplify, [], [normalize_0_0, normalize_0_4])).
-- cnf(refute_0_0, plain, ($false),
--     inference(canonicalize, [], [normalize_0_5])).

-- subgoal_0 : (z : D)
-- subgoal_0 = strip a4
strip-0 = id

-- negate_0_0 : {z : D}(~ z)
-- negate_0_0 = negate subgoal_0
-- negate-0-0 = proofByContradiction

-- normalize_0_0 : {z : D}(~ z)
-- normalize_0_0  = canonicalize negate_0_0
canonicalize-0 = id

-- normalize_0_1 :  { A B Z : D } (~ a | ~ b | z)
-- normalize_0_1(~ a | ~ b | z) = canonicalize a3
postulate canonicalize-1 : { A B Z : Set } → (A ∧ B → Z) → ¬ A ∨ ¬ B ∨ Z


-- normalize_0_2 : (a : D)
-- normalize_0_2 = canonicalize a1
canonicalize-2 = id

-- normalize_0_3 : (b : D)
-- normalize_0_3 = canonicalize a2
canonicalize-3 = id

-- normalize_0_4 : (z : D)
-- normalize_0_4 = simplify normalize_0_1 normalize_0_2 normalize_0_3
postulate simplify-0 : { A B Z : Set } → A → B → ¬ A ∨ ¬ B ∨ Z → Z

-- normalize_0_5 : ⊥
-- normalize_0_5 = simplify normalize_0_0 normalize_0_4
simplify-1 :{Z : Set} →  ¬ Z → Z → ⊥
simplify-1 f z = f z

-- refute_0_0 : ⊥
-- refute_0_0 = canonicalize normalize_0_5
canonicalize-4 = id

-- conclude_0 : z
-- conclude_0 = contradiction negate-0
proof : { A B Z : Set } → A → B → ( A ∧ B → Z ) → Z
proof {_}{_}{Z} a1 a2 a3 = conclude-0
  where
    normalize-0-3 = canonicalize-3 a2
    normalize-0-2 = canonicalize-2 a1
    normalize-0-1 = canonicalize-1 a3
    normalize-0-4 = simplify-0 normalize-0-2 normalize-0-3 normalize-0-1
    negate-0 : ¬ Z → ⊥
    negate-0 negatate-0-0 = refute-0-0
      where
        normalize-0-0 = id negatate-0-0
        normalize-0-5 = simplify-1 normalize-0-0 normalize-0-4
        refute-0-0 = canonicalize-4 normalize-0-5
    conclude-0 = proofByContradiction negate-0
