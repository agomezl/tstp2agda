
-- tstp2agda proof

open import Data.FOL.Deep 2 public
open import Data.FOL.Deep.ATP.Metis 2 public

-- Vars
p : Prop
p = Var (# 0)

q : Prop
q = Var (# 1)

-- Premise
Γ : Ctxt
Γ = ∅

-- Conjecture
goal : Prop
goal = ((p ⇔ q) ⇔ ((q ∨ ¬ p) ∧ (¬ q ∨ p)))

-- Subgoals
subgoal₀ : Prop
subgoal₀ = (((p ⇔ q) ∧ ¬ q) ⇒ ¬ p)

subgoal₁ : Prop
subgoal₁ = ((((p ⇔ q) ∧ (q ∨ ¬ p)) ∧ ¬ ¬ q) ⇒ p)

subgoal₂ : Prop
subgoal₂ = ((((q ∨ ¬ p) ∧ (¬ q ∨ p)) ∧ p) ⇒ q)

subgoal₃ : Prop
subgoal₃ = ((((q ∨ ¬ p) ∧ (¬ q ∨ p)) ∧ q) ⇒ p)

-- Metis Proof.
proof₀ : Γ ⊢ subgoal₀
proof₀ =
 RAA $
    atp-canonicalize $
      atp-simplify $ ∧-intro
        (
        ? -- inference rule no supported yet $
          atp-canonicalize $
            atp-strip $
              assume {Γ = Γ} $
                atp-neg subgoal₀
        )
        (
        ? -- inference rule no supported yet $
          atp-canonicalize $
            atp-strip $
              assume {Γ = Γ} $
                atp-neg subgoal₀
        )
        (
        ? -- inference rule no supported yet $
          atp-canonicalize $
            atp-strip $
              assume {Γ = Γ} $
                atp-neg subgoal₀
        )

proof₁ : Γ ⊢ subgoal₁
proof₁ =
 RAA $
    atp-canonicalize $
      atp-simplify $ ∧-intro
        (
        ? -- inference rule no supported yet $
          atp-canonicalize $
            atp-strip $
              assume {Γ = Γ} $
                atp-neg subgoal₁
        )
        (
        ? -- inference rule no supported yet $
          atp-canonicalize $
            atp-strip $
              assume {Γ = Γ} $
                atp-neg subgoal₁
        )
        (
        ? -- inference rule no supported yet $
          atp-canonicalize $
            atp-strip $
              assume {Γ = Γ} $
                atp-neg subgoal₁
        )

proof₂ : Γ ⊢ subgoal₂
proof₂ =
 RAA $
    atp-canonicalize $
      atp-simplify $ ∧-intro
        (
        ? -- inference rule no supported yet $
          atp-canonicalize $
            atp-strip $
              assume {Γ = Γ} $
                atp-neg subgoal₂
        )
        (
        ? -- inference rule no supported yet $
          atp-canonicalize $
            atp-strip $
              assume {Γ = Γ} $
                atp-neg subgoal₂
        )
        (
        ? -- inference rule no supported yet $
          atp-canonicalize $
            atp-strip $
              assume {Γ = Γ} $
                atp-neg subgoal₂
        )

proof₃ : Γ ⊢ subgoal₃
proof₃ =
 RAA $
    atp-canonicalize $
      atp-simplify $ ∧-intro
        (
        ? -- inference rule no supported yet $
          atp-canonicalize $
            atp-strip $
              assume {Γ = Γ} $
                atp-neg subgoal₃
        )
        (
        ? -- inference rule no supported yet $
          atp-canonicalize $
            atp-strip $
              assume {Γ = Γ} $
                atp-neg subgoal₃
        )
        (
        ? -- inference rule no supported yet $
          atp-canonicalize $
            atp-strip $
              assume {Γ = Γ} $
                atp-neg subgoal₃
        )

proof : Γ ⊢ goal
proof = ? -- Not supported yet

