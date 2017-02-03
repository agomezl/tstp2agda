

--
-- Examples
-- axiom a
-- axiom b
-- axiom ¬ a ∨ ¬ b ∨ c
-- conjecture ¬ c ∨ d

Basic2 : ∀ {a b c d : Prop} → ([] , a , b , ¬ a ∨ ¬ b ∨ c , ¬ c ∨ d) ⊢ d
Basic2 = {!!}

open import Function using (id)