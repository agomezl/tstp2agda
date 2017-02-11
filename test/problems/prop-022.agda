
-- tstp2agda proof

open import Data.FOL.Deep 3
open import Data.FOL.Deep.ATP.Metis 3

-- Vars
p : Prop
p = Var (# 0)

q : Prop
q = Var (# 1)

r : Prop
r = Var (# 2)

-- Premise
Γ : Ctxt
Γ = ∅

-- Conjecture
goal : Prop
goal = (((p ⇔ q) ⇔ r) ⇔ (p ⇔ (q ⇔ r)))

-- Subgoals
subgoal₀ : Prop
subgoal₀ = (((((p ⇔ q) ⇔ r) ∧ p) ∧ q) ⇒ r)

subgoal₁ : Prop
subgoal₁ = (((((p ⇔ q) ⇔ r) ∧ p) ∧ r) ⇒ q)

subgoal₂ : Prop
subgoal₂ = ((((p ⇔ q) ⇔ r) ∧ (q ⇔ r)) ⇒ p)

subgoal₃ : Prop
subgoal₃ = (((p ⇔ (q ⇔ r)) ∧ (p ⇔ q)) ⇒ r)

subgoal₄ : Prop
subgoal₄ = ((((p ⇔ (q ⇔ r)) ∧ r) ∧ p) ⇒ q)

subgoal₅ : Prop
subgoal₅ = ((((p ⇔ (q ⇔ r)) ∧ r) ∧ q) ⇒ p)

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



proof₁ : Γ ⊢ subgoal₁
proof₁ =
  RAA $
    atp-canonicalize $
      atp-simplify $ ∧-intro
        (
        inference rule no supported yet $
          atp-canonicalize $
            atp-strip $
              assume {Γ = Γ} $
                atp-neg subgoal₁        )
        (
        inference rule no supported yet $
          atp-canonicalize $
            atp-strip $
              assume {Γ = Γ} $
                atp-neg subgoal₁        )
        (
        inference rule no supported yet $
          atp-canonicalize $
            atp-strip $
              assume {Γ = Γ} $
                atp-neg subgoal₁        )
        (
        inference rule no supported yet $
          atp-canonicalize $
            atp-strip $
              assume {Γ = Γ} $
                atp-neg subgoal₁        )



proof₂ : Γ ⊢ subgoal₂
proof₂ =
  RAA $
    atp-canonicalize $
      atp-simplify $ ∧-intro
        (
        inference rule no supported yet $
          atp-canonicalize $
            atp-strip $
              assume {Γ = Γ} $
                atp-neg subgoal₂        )
        (
        inference rule no supported yet $
          atp-canonicalize $
            atp-strip $
              assume {Γ = Γ} $
                atp-neg subgoal₂        )
        (
        inference rule no supported yet $
          atp-canonicalize $
            atp-strip $
              assume {Γ = Γ} $
                atp-neg subgoal₂        )



proof₃ : Γ ⊢ subgoal₃
proof₃ =
  RAA $
    atp-canonicalize $
      atp-simplify $ ∧-intro
        (
        inference rule no supported yet $
          atp-canonicalize $
            atp-strip $
              assume {Γ = Γ} $
                atp-neg subgoal₃        )
        (
        inference rule no supported yet $
          atp-canonicalize $
            atp-strip $
              assume {Γ = Γ} $
                atp-neg subgoal₃        )
        (
        inference rule no supported yet $
          atp-canonicalize $
            atp-strip $
              assume {Γ = Γ} $
                atp-neg subgoal₃        )



proof₄ : Γ ⊢ subgoal₄
proof₄ =
  RAA $
    atp-canonicalize $
      atp-simplify $ ∧-intro
        (
        inference rule no supported yet $
          atp-canonicalize $
            atp-strip $
              assume {Γ = Γ} $
                atp-neg subgoal₄        )
        (
        inference rule no supported yet $
          atp-canonicalize $
            atp-strip $
              assume {Γ = Γ} $
                atp-neg subgoal₄        )
        (
        inference rule no supported yet $
          atp-canonicalize $
            atp-strip $
              assume {Γ = Γ} $
                atp-neg subgoal₄        )
        (
        inference rule no supported yet $
          atp-canonicalize $
            atp-strip $
              assume {Γ = Γ} $
                atp-neg subgoal₄        )



proof₅ : Γ ⊢ subgoal₅
proof₅ =
  RAA $
    atp-canonicalize $
      atp-simplify $ ∧-intro
        (
        inference rule no supported yet $
          atp-canonicalize $
            atp-strip $
              assume {Γ = Γ} $
                atp-neg subgoal₅        )
        (
        inference rule no supported yet $
          atp-canonicalize $
            atp-strip $
              assume {Γ = Γ} $
                atp-neg subgoal₅        )
        (
        inference rule no supported yet $
          atp-canonicalize $
            atp-strip $
              assume {Γ = Γ} $
                atp-neg subgoal₅        )
        (
        inference rule no supported yet $
          atp-canonicalize $
            atp-strip $
              assume {Γ = Γ} $
                atp-neg subgoal₅        )



