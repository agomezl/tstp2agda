
-- tstp2agda proof

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
