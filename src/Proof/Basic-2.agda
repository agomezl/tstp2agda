module Proof.Basic-2 where

open import Data.FOL.Shallow
open import Function using (id)

-- fof(a1, axiom, (a)).
-- fof(a2, axiom, (b)).
-- fof(a3, axiom, (~ a | ~ b | c)).
-- fof(a4, axiom, (~ c | d)).
-- fof(a5, conjecture, (d)).
-- fof(subgoal_0, plain, (d), inference(strip, [], [a5])).
-- fof(negate_0_0, plain, (~ d),
--     inference(negate, [], [subgoal_0])).
-- fof(normalize_0_0, plain, (~ d),
--     inference(canonicalize, [], [negate_0_0])).
-- fof(normalize_0_1, plain, (~ c | d),
--     inference(canonicalize, [], [a4])).
-- fof(normalize_0_2, plain, (~ a | ~ b | c),
--     inference(canonicalize, [], [a3])).
-- fof(normalize_0_3, plain, (a),
--     inference(canonicalize, [], [a1])).
-- fof(normalize_0_4, plain, (b),
--     inference(canonicalize, [], [a2])).
-- fof(normalize_0_5, plain, (c),
--     inference(simplify, [],[normalize_0_2, normalize_0_3, normalize_0_4])).
-- fof(normalize_0_6, plain, (d),
--     inference(simplify, [],[normalize_0_1, normalize_0_5])).
-- fof(normalize_0_7, plain, ($false),
--     inference(simplify, [], [normalize_0_0, normalize_0_6])).
-- cnf(refute_0_0, plain, ($false),
--     inference(canonicalize, [], [normalize_0_7])).

canonicalize-0 = id
canonicalize-1 = id
canonicalize-2 = id
canonicalize-3 = id
canonicalize-4 = id
canonicalize-5 = id

simplify-0 : {D : Set} → ¬ D → D → ⊥
simplify-0 nd d = nd d

simplify-2 : {A B C : Set} → ¬ A ∨ ¬ B ∨ C → A → B → C
simplify-2 (inj₁ na) a _ = ⊥-elim (na a)
simplify-2 (inj₂ x ) _ b with x
... | (inj₁ nb) =  ⊥-elim (nb b)
... | (inj₂ c)  =  c

simplify-1 : {C D   : Set} → ¬ C ∨ D → C → D
simplify-1 (inj₁ nc) c = ⊥-elim (nc c)
simplify-1 (inj₂ d)  _ = d

proof : {A B C D : Set} → A → B →  ¬ A ∨ ¬ B ∨ C → ¬ C ∨ D → D
proof {_}{_}{_}{D} a1 a2 a3 a4 = conclude-0
  where
    normalize-0-1 = canonicalize-5 a4
    normalize-0-2 = canonicalize-4 a3
    normalize-0-3 = canonicalize-3 a1
    normalize-0-4 = canonicalize-2 a2
    normalize-0-5 = simplify-2 normalize-0-2 normalize-0-3 normalize-0-4
    normalize-0-6 = simplify-1 normalize-0-1 normalize-0-5
    negate-0 : ¬ D → ⊥
    negate-0 negate-0-0 = refute-0-0
      where
        normalize-0-0 = canonicalize-1 negate-0-0
        normalize-0-7 = simplify-0 normalize-0-0 normalize-0-6
        refute-0-0    = canonicalize-0 normalize-0-7
    conclude-0 = proofByContradiction negate-0
