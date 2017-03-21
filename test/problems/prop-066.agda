
-- tstp2agda proof

open import Data.FOL.Deep 5 public
open import Data.FOL.Deep.ATP.Metis 5 public

-- Vars
p1 : Prop
p1 = Var (# 0)

p2 : Prop
p2 = Var (# 1)

p3 : Prop
p3 = Var (# 2)

p4 : Prop
p4 = Var (# 3)

p5 : Prop
p5 = Var (# 4)

-- Axiom
a₁ : Prop
a₁ = ((((p1 ∧ p2) ∧ p3) ∧ p4) ∧ p5)


-- Premise
Γ : Ctxt
Γ = [ a1 ]

-- Conjecture
goal : Prop
goal = (p1 ∧ p1)


-- Subgoals
subgoal₀ : Prop
subgoal₀ = p1


subgoal₁ : Prop
subgoal₁ = (p1 ⇒ p1)

-- Metis Proof.
proof₀ : Γ ⊢ subgoal₀
proof₀ =
  RAA $
    atp-canonicalize $  -- Γ ⊢ ⊥
      atp-simplify $  -- Γ ⊢ ⊥
        ∧-intro
          (
          atp-canonicalize $  -- Γ ⊢ ¬ p1
            atp-strip $  -- Γ ⊢ p1
              assume {Γ = Γ} $  -- Γ ⊢ ¬ p1
                atp-neg subgoal₀
          )
          (
          ∧-proj₁ $ -- 1: (((p1 ∧ p2) ∧ p3) ∧ p4)
            atp-canonicalize $  -- Γ ⊢ ((((p1 ∧ p2) ∧ p3) ∧ p4) ∧ p5)
              weaken (atp-neg subgoal₀) $
                (assume {Γ = ∅} a1)
          )

proof₁ : Γ ⊢ subgoal₁
proof₁ =
  RAA $
    atp-canonicalize $  -- Γ ⊢ ⊥
      atp-canonicalize $  -- Γ ⊢ ⊥
        atp-strip $  -- Γ ⊢ (p1 ⇒ p1)
          assume {Γ = Γ} $  -- Γ ⊢ ¬ (p1 ⇒ p1)
            atp-neg subgoal₁

proof : Γ ⊢ goal
proof =
  ⇒-elim
    atp-splitGoal
    (
    ∧-intro
      subgoal₀
      subgoal₁
    )

