
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
    atp-canonicalize $  -- Γ ⊢ ⊥
      atp-simplify $  -- Γ ⊢ ⊥
        ∧-intro
          (
          atp-conjunct $  -- Γ ⊢ (¬ p ⇔ ¬ q)
            atp-canonicalize $  -- Γ ⊢ ((¬ q ∧ p) ∧ (¬ p ⇔ ¬ q))
              atp-strip $  -- Γ ⊢ (((p ⇔ q) ∧ ¬ q) ⇒ ¬ p)
                assume {Γ = Γ} $  -- Γ ⊢ ¬ (((p ⇔ q) ∧ ¬ q) ⇒ ¬ p)
                  atp-neg subgoal₀
          )
          (
          ∧-intro
            (
            atp-conjunct $  -- Γ ⊢ p
              atp-canonicalize $  -- Γ ⊢ ((¬ q ∧ p) ∧ (¬ p ⇔ ¬ q))
                atp-strip $  -- Γ ⊢ (((p ⇔ q) ∧ ¬ q) ⇒ ¬ p)
                  assume {Γ = Γ} $  -- Γ ⊢ ¬ (((p ⇔ q) ∧ ¬ q) ⇒ ¬ p)
                    atp-neg subgoal₀
            )
            (
            atp-conjunct $  -- Γ ⊢ ¬ q
              atp-canonicalize $  -- Γ ⊢ ((¬ q ∧ p) ∧ (¬ p ⇔ ¬ q))
                atp-strip $  -- Γ ⊢ (((p ⇔ q) ∧ ¬ q) ⇒ ¬ p)
                  assume {Γ = Γ} $  -- Γ ⊢ ¬ (((p ⇔ q) ∧ ¬ q) ⇒ ¬ p)
                    atp-neg subgoal₀
            )
          )

proof₁ : Γ ⊢ subgoal₁
proof₁ =
  RAA $
    atp-canonicalize $  -- Γ ⊢ ⊥
      atp-simplify $  -- Γ ⊢ ⊥
        ∧-intro
          (
          atp-conjunct $  -- Γ ⊢ (¬ p ⇔ ¬ q)
            atp-canonicalize $  -- Γ ⊢ (((¬ p ∧ q) ∧ (¬ p ∨ q)) ∧ (¬ p ⇔ ¬ q))
              atp-strip $  -- Γ ⊢ ((((p ⇔ q) ∧ (q ∨ ¬ p)) ∧ ¬ ¬ q) ⇒ p)
                assume {Γ = Γ} $  -- Γ ⊢ ¬ ((((p ⇔ q) ∧ (q ∨ ¬ p)) ∧ ¬ ¬ q) ⇒ p)
                  atp-neg subgoal₁
          )
          (
          ∧-intro
            (
            atp-conjunct $  -- Γ ⊢ ¬ p
              atp-canonicalize $  -- Γ ⊢ (((¬ p ∧ q) ∧ (¬ p ∨ q)) ∧ (¬ p ⇔ ¬ q))
                atp-strip $  -- Γ ⊢ ((((p ⇔ q) ∧ (q ∨ ¬ p)) ∧ ¬ ¬ q) ⇒ p)
                  assume {Γ = Γ} $  -- Γ ⊢ ¬ ((((p ⇔ q) ∧ (q ∨ ¬ p)) ∧ ¬ ¬ q) ⇒ p)
                    atp-neg subgoal₁
            )
            (
            atp-conjunct $  -- Γ ⊢ q
              atp-canonicalize $  -- Γ ⊢ (((¬ p ∧ q) ∧ (¬ p ∨ q)) ∧ (¬ p ⇔ ¬ q))
                atp-strip $  -- Γ ⊢ ((((p ⇔ q) ∧ (q ∨ ¬ p)) ∧ ¬ ¬ q) ⇒ p)
                  assume {Γ = Γ} $  -- Γ ⊢ ¬ ((((p ⇔ q) ∧ (q ∨ ¬ p)) ∧ ¬ ¬ q) ⇒ p)
                    atp-neg subgoal₁
            )
          )

proof₂ : Γ ⊢ subgoal₂
proof₂ =
  RAA $
    atp-canonicalize $  -- Γ ⊢ ⊥
      atp-simplify $  -- Γ ⊢ ⊥
        ∧-intro
          (
          atp-conjunct $  -- Γ ⊢ (¬ p ∨ q)
            atp-canonicalize $  -- Γ ⊢ (((¬ q ∧ p) ∧ (¬ p ∨ q)) ∧ (¬ q ∨ p))
              atp-strip $  -- Γ ⊢ ((((q ∨ ¬ p) ∧ (¬ q ∨ p)) ∧ p) ⇒ q)
                assume {Γ = Γ} $  -- Γ ⊢ ¬ ((((q ∨ ¬ p) ∧ (¬ q ∨ p)) ∧ p) ⇒ q)
                  atp-neg subgoal₂
          )
          (
          ∧-intro
            (
            atp-conjunct $  -- Γ ⊢ p
              atp-canonicalize $  -- Γ ⊢ (((¬ q ∧ p) ∧ (¬ p ∨ q)) ∧ (¬ q ∨ p))
                atp-strip $  -- Γ ⊢ ((((q ∨ ¬ p) ∧ (¬ q ∨ p)) ∧ p) ⇒ q)
                  assume {Γ = Γ} $  -- Γ ⊢ ¬ ((((q ∨ ¬ p) ∧ (¬ q ∨ p)) ∧ p) ⇒ q)
                    atp-neg subgoal₂
            )
            (
            atp-conjunct $  -- Γ ⊢ ¬ q
              atp-canonicalize $  -- Γ ⊢ (((¬ q ∧ p) ∧ (¬ p ∨ q)) ∧ (¬ q ∨ p))
                atp-strip $  -- Γ ⊢ ((((q ∨ ¬ p) ∧ (¬ q ∨ p)) ∧ p) ⇒ q)
                  assume {Γ = Γ} $  -- Γ ⊢ ¬ ((((q ∨ ¬ p) ∧ (¬ q ∨ p)) ∧ p) ⇒ q)
                    atp-neg subgoal₂
            )
          )

proof₃ : Γ ⊢ subgoal₃
proof₃ =
  RAA $
    atp-canonicalize $  -- Γ ⊢ ⊥
      atp-simplify $  -- Γ ⊢ ⊥
        ∧-intro
          (
          atp-conjunct $  -- Γ ⊢ (¬ q ∨ p)
            atp-canonicalize $  -- Γ ⊢ (((¬ p ∧ q) ∧ (¬ p ∨ q)) ∧ (¬ q ∨ p))
              atp-strip $  -- Γ ⊢ ((((q ∨ ¬ p) ∧ (¬ q ∨ p)) ∧ q) ⇒ p)
                assume {Γ = Γ} $  -- Γ ⊢ ¬ ((((q ∨ ¬ p) ∧ (¬ q ∨ p)) ∧ q) ⇒ p)
                  atp-neg subgoal₃
          )
          (
          ∧-intro
            (
            atp-conjunct $  -- Γ ⊢ q
              atp-canonicalize $  -- Γ ⊢ (((¬ p ∧ q) ∧ (¬ p ∨ q)) ∧ (¬ q ∨ p))
                atp-strip $  -- Γ ⊢ ((((q ∨ ¬ p) ∧ (¬ q ∨ p)) ∧ q) ⇒ p)
                  assume {Γ = Γ} $  -- Γ ⊢ ¬ ((((q ∨ ¬ p) ∧ (¬ q ∨ p)) ∧ q) ⇒ p)
                    atp-neg subgoal₃
            )
            (
            atp-conjunct $  -- Γ ⊢ ¬ p
              atp-canonicalize $  -- Γ ⊢ (((¬ p ∧ q) ∧ (¬ p ∨ q)) ∧ (¬ q ∨ p))
                atp-strip $  -- Γ ⊢ ((((q ∨ ¬ p) ∧ (¬ q ∨ p)) ∧ q) ⇒ p)
                  assume {Γ = Γ} $  -- Γ ⊢ ¬ ((((q ∨ ¬ p) ∧ (¬ q ∨ p)) ∧ q) ⇒ p)
                    atp-neg subgoal₃
            )
          )

proof : Γ ⊢ goal
proof =
  ⇒-elim
    atp-splitGoal
    (
    ∧-intro
      subgoal₀
      (
      ∧-intro
        subgoal₁
        (
        ∧-intro
          subgoal₂
          subgoal₃
        )
      )
    )

