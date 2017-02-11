
-- tstp2agda proof

open import Data.FOL.Deep 3
open import Data.FOL.Deep.ATP.Metis 3

-- Vars
s : Prop
s = Var (# 0)

x : Prop
x = Var (# 1)

y : Prop
y = Var (# 2)

-- Premise
Γ : Ctxt
Γ = ∅

-- Conjecture
goal : Prop
goal = (((s ⇒ x) ∧ (s ⇒ (x ⇒ y))) ⇒ (s ⇒ y))

-- Subgoal
subgoal₀ : Prop
subgoal₀ = ((((s ⇒ x) ∧ (s ⇒ (x ⇒ y))) ∧ s) ⇒ y)

-- Metis Proof.
proof₀ : Γ ⊢ subgoal₀
proof₀ =
  RAA $
    atp-canonicalize $
      atp-simplify $ ∧-intro
        (
        inference rule no supported yet $
          atp-canonicalize $
            atp-strip $
              assume {Γ = Γ} $
                atp-neg subgoal₀        )
        (
        inference rule no supported yet $
          atp-canonicalize $
            atp-strip $
              assume {Γ = Γ} $
                atp-neg subgoal₀        )
        (
        atp-simplify $ ∧-intro
          (
          inference rule no supported yet $
            atp-canonicalize $
              atp-strip $
                assume {Γ = Γ} $
                  atp-neg subgoal₀          )
          (
          inference rule no supported yet $
            atp-canonicalize $
              atp-strip $
                assume {Γ = Γ} $
                  atp-neg subgoal₀          )
        )
        (
        inference rule no supported yet $
          atp-canonicalize $
            atp-strip $
              assume {Γ = Γ} $
                atp-neg subgoal₀        )



