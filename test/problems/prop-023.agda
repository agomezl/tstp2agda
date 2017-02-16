
-- tstp2agda proof

open import Data.FOL.Deep 3 public
open import Data.FOL.Deep.ATP.Metis 3 public

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
goal = ((p ∨ (q ∧ r)) ⇔ ((p ∨ q) ∧ (p ∨ r)))


-- Subgoals
subgoal₀ : Prop
subgoal₀ = (((p ∨ (q ∧ r)) ∧ ¬ p) ⇒ q)


subgoal₁ : Prop
subgoal₁ = ((((p ∨ (q ∧ r)) ∧ (p ∨ q)) ∧ ¬ p) ⇒ r)


subgoal₂ : Prop
subgoal₂ = ((((p ∨ q) ∧ (p ∨ r)) ∧ ¬ p) ⇒ q)


subgoal₃ : Prop
subgoal₃ = (((((p ∨ q) ∧ (p ∨ r)) ∧ ¬ p) ∧ q) ⇒ r)

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

