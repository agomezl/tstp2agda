
-- tstp2agda proof

open import Data.FOL.Shallow
open import Function using (id)

postulate fun-normalize-0-0 : {p q r : Set} → ¬ ((p ∨ q → p ∨ r) ∧ ¬ p ∧ q → r) → ¬ p ∧ ¬ r ∧ q ∧ p ∨ r ∨ ¬ p ∧ ¬ q

postulate fun-normalize-0-1 : {p q r : Set} → ¬ p ∧ ¬ r ∧ q ∧ p ∨ r ∨ ¬ p ∧ ¬ q → p ∨ r ∨ ¬ p ∧ ¬ q

postulate fun-normalize-0-2 : {p q r : Set} → ¬ p ∧ ¬ r ∧ q ∧ p ∨ r ∨ ¬ p ∧ ¬ q → ¬ p

postulate fun-normalize-0-3 : {p q r : Set} → ¬ p ∧ ¬ r ∧ q ∧ p ∨ r ∨ ¬ p ∧ ¬ q → ¬ r

postulate fun-normalize-0-4 : {p q r : Set} → ¬ p ∧ ¬ r ∧ q ∧ p ∨ r ∨ ¬ p ∧ ¬ q → q

postulate fun-normalize-0-5 : {p q r : Set} → p ∨ r ∨ ¬ p ∧ ¬ q → ¬ p → ¬ r → ¬ p → q → $false

postulate fun-refute-0-0 :  $false → $false

postulate goals : {p q r : Set} → ((p ∨ q → p ∨ r) ∧ ¬ p ∧ q → r) → ((p ∨ q → p ∨ r) → p ∨ (q → r))

proof : {p q r : Set} → ((p ∨ q → p ∨ r) → p ∨ (q → r))
proof {p}{q}{r} = goals subgoal-0
  where
    fun-negate-0-0 : ¬ ((p ∨ q → p ∨ r) ∧ ¬ p ∧ q → r) → $false
    fun-negate-0-0 negate-0-0 = refute-0-0
      where
        normalize-0-0 = fun-normalize-0-0 negate-0-0
        normalize-0-1 = fun-normalize-0-1 normalize-0-0
        normalize-0-2 = fun-normalize-0-2 normalize-0-0
        normalize-0-3 = fun-normalize-0-3 normalize-0-0
        normalize-0-4 = fun-normalize-0-4 normalize-0-0
        normalize-0-5 = fun-normalize-0-5 normalize-0-1 normalize-0-2 normalize-0-3 normalize-0-2 normalize-0-4
        refute-0-0 = fun-refute-0-0 normalize-0-5
    subgoal-0 = proofByContradiction fun-negate-0-0
