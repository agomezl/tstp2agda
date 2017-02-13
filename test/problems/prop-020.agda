
-- tstp2agda proof

open import Data.FOL.Shallow
open import Function using (id)

postulate fun-normalize-0-0 : {p q r : Set} → ¬ ((q → r) ∧ (r → p ∧ q) ∧ (p → q ∧ r) ∧ p → q) → ¬ q ∧ p ∧ ¬ p ∨ q ∧ r ∧ ¬ q ∨ r ∧ ¬ r ∨ p ∧ q

postulate fun-normalize-0-1 : {p q r : Set} → ¬ q ∧ p ∧ ¬ p ∨ q ∧ r ∧ ¬ q ∨ r ∧ ¬ r ∨ p ∧ q → ¬ p ∨ q ∧ r

postulate fun-normalize-0-2 : {p q r : Set} → ¬ q ∧ p ∧ ¬ p ∨ q ∧ r ∧ ¬ q ∨ r ∧ ¬ r ∨ p ∧ q → p

postulate fun-normalize-0-3 : {p q r : Set} → ¬ q ∧ p ∧ ¬ p ∨ q ∧ r ∧ ¬ q ∨ r ∧ ¬ r ∨ p ∧ q → ¬ q

postulate fun-normalize-0-4 : {p q r : Set} → ¬ p ∨ q ∧ r → p → ¬ q → ⊥

postulate fun-normalize-1-0 : {p q r : Set} → ¬ ((q → r) ∧ (r → p ∧ q) ∧ (p → q ∧ r) ∧ q → p) → ¬ p ∧ q ∧ ¬ p ∨ q ∧ r ∧ ¬ q ∨ r ∧ ¬ r ∨ p ∧ q

postulate fun-normalize-1-1 : {p q r : Set} → ¬ p ∧ q ∧ ¬ p ∨ q ∧ r ∧ ¬ q ∨ r ∧ ¬ r ∨ p ∧ q → ¬ r ∨ p ∧ q

postulate fun-normalize-1-2 : {p q r : Set} → ¬ p ∧ q ∧ ¬ p ∨ q ∧ r ∧ ¬ q ∨ r ∧ ¬ r ∨ p ∧ q → ¬ q ∨ r

postulate fun-normalize-1-3 : {p q r : Set} → ¬ p ∧ q ∧ ¬ p ∨ q ∧ r ∧ ¬ q ∨ r ∧ ¬ r ∨ p ∧ q → q

postulate fun-normalize-1-4 : {q r : Set} → ¬ q ∨ r → q → r

postulate fun-normalize-1-5 : {p q r : Set} → ¬ p ∧ q ∧ ¬ p ∨ q ∧ r ∧ ¬ q ∨ r ∧ ¬ r ∨ p ∧ q → ¬ p

postulate fun-normalize-1-6 : {p q r : Set} → ¬ r ∨ p ∧ q → r → ¬ p → q → ⊥

postulate fun-refute-0-0 :  ⊥ → ⊥

postulate fun-refute-1-0 :  ⊥ → ⊥

postulate goals : {p q r : Set} → ((q → r) ∧ (r → p ∧ q) ∧ (p → q ∧ r) ∧ p → q) → ((q → r) ∧ (r → p ∧ q) ∧ (p → q ∧ r) ∧ q → p) → ((q → r) ∧ (r → p ∧ q) ∧ (p → q ∧ r) → p ↔ q)

proof : {p q r : Set} → ((q → r) ∧ (r → p ∧ q) ∧ (p → q ∧ r) → p ↔ q)
proof {p}{q}{r} = goals subgoal-0 subgoal-1
  where
    fun-negate-0-0 : ¬ ((q → r) ∧ (r → p ∧ q) ∧ (p → q ∧ r) ∧ p → q) → ⊥
    fun-negate-0-0 negate-0-0 = refute-0-0
      where
        normalize-0-0 = fun-normalize-0-0 negate-0-0
        normalize-0-1 = fun-normalize-0-1 normalize-0-0
        normalize-0-2 = fun-normalize-0-2 normalize-0-0
        normalize-0-3 = fun-normalize-0-3 normalize-0-0
        normalize-0-4 = fun-normalize-0-4 normalize-0-1 normalize-0-2 normalize-0-3
        refute-0-0 = fun-refute-0-0 normalize-0-4
    subgoal-0 = proofByContradiction fun-negate-0-0
    fun-negate-1-0 : ¬ ((q → r) ∧ (r → p ∧ q) ∧ (p → q ∧ r) ∧ q → p) → ⊥
    fun-negate-1-0 negate-1-0 = refute-1-0
      where
        normalize-1-0 = fun-normalize-1-0 negate-1-0
        normalize-1-1 = fun-normalize-1-1 normalize-1-0
        normalize-1-2 = fun-normalize-1-2 normalize-1-0
        normalize-1-3 = fun-normalize-1-3 normalize-1-0
        normalize-1-4 = fun-normalize-1-4 normalize-1-2 normalize-1-3
        normalize-1-5 = fun-normalize-1-5 normalize-1-0
        normalize-1-6 = fun-normalize-1-6 normalize-1-1 normalize-1-4 normalize-1-5 normalize-1-3
        refute-1-0 = fun-refute-1-0 normalize-1-6
    subgoal-1 = proofByContradiction fun-negate-1-0
