
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
goal = (¬ (¬ (p ⇔ q) ⇔ r) ⇔ ¬ (p ⇔ ¬ (q ⇔ r)))


-- Subgoals
subgoal₀ : Prop
subgoal₀ = (((¬ (¬ (p ⇔ q) ⇔ r) ∧ p) ∧ q) ⇒ r)


subgoal₁ : Prop
subgoal₁ = (((¬ (¬ (p ⇔ q) ⇔ r) ∧ p) ∧ r) ⇒ q)


subgoal₂ : Prop
subgoal₂ = ((¬ (¬ (p ⇔ q) ⇔ r) ∧ ¬ (q ⇔ r)) ⇒ ¬ p)


subgoal₃ : Prop
subgoal₃ = ((¬ (p ⇔ ¬ (q ⇔ r)) ∧ ¬ (p ⇔ q)) ⇒ ¬ r)


subgoal₄ : Prop
subgoal₄ = (((¬ (p ⇔ ¬ (q ⇔ r)) ∧ r) ∧ p) ⇒ q)


subgoal₅ : Prop
subgoal₅ = (((¬ (p ⇔ ¬ (q ⇔ r)) ∧ r) ∧ q) ⇒ p)

-- Metis Proof.
proof₀ : Γ ⊢ subgoal₀
proof₀ =
  RAA $
  -- Γ , ¬ subgoal₀⊢ ⊥
    atp-canonicalize $
      atp-simplify $
        ∧-intro
          (
          atp-conjunct $
            atp-canonicalize $
              atp-strip $
                assume {Γ = Γ} $
                  atp-neg subgoal₀
          )
          (
          ∧-intro
            (
            atp-conjunct $
              atp-canonicalize $
                atp-strip $
                  assume {Γ = Γ} $
                    atp-neg subgoal₀
            )
            (
            ∧-intro
              (
              atp-conjunct $
                atp-canonicalize $
                  atp-strip $
                    assume {Γ = Γ} $
                      atp-neg subgoal₀
              )
              (
              atp-conjunct $
                atp-canonicalize $
                  atp-strip $
                    assume {Γ = Γ} $
                      atp-neg subgoal₀
              )
            )
          )

proof₁ : Γ ⊢ subgoal₁
proof₁ =
  RAA $
  -- Γ , ¬ subgoal₁⊢ ⊥
    atp-canonicalize $
      atp-simplify $
        ∧-intro
          (
          atp-conjunct $
            atp-canonicalize $
              atp-strip $
                assume {Γ = Γ} $
                  atp-neg subgoal₁
          )
          (
          ∧-intro
            (
            atp-conjunct $
              atp-canonicalize $
                atp-strip $
                  assume {Γ = Γ} $
                    atp-neg subgoal₁
            )
            (
            ∧-intro
              (
              atp-conjunct $
                atp-canonicalize $
                  atp-strip $
                    assume {Γ = Γ} $
                      atp-neg subgoal₁
              )
              (
              atp-conjunct $
                atp-canonicalize $
                  atp-strip $
                    assume {Γ = Γ} $
                      atp-neg subgoal₁
              )
            )
          )

proof₂ : Γ ⊢ subgoal₂
proof₂ =
  RAA $
  -- Γ , ¬ subgoal₂⊢ ⊥
    atp-canonicalize $
      atp-simplify $
        ∧-intro
          (
          atp-conjunct $
            atp-canonicalize $
              atp-strip $
                assume {Γ = Γ} $
                  atp-neg subgoal₂
          )
          (
          atp-simplify $
            ∧-intro
              (
              atp-conjunct $
                atp-canonicalize $
                  atp-strip $
                    assume {Γ = Γ} $
                      atp-neg subgoal₂
              )
              (
              atp-conjunct $
                atp-canonicalize $
                  atp-strip $
                    assume {Γ = Γ} $
                      atp-neg subgoal₂
              )
          )

proof₃ : Γ ⊢ subgoal₃
proof₃ =
  RAA $
  -- Γ , ¬ subgoal₃⊢ ⊥
    atp-canonicalize $
      atp-simplify $
        ∧-intro
          (
          atp-conjunct $
            atp-canonicalize $
              atp-strip $
                assume {Γ = Γ} $
                  atp-neg subgoal₃
          )
          (
          atp-simplify $
            ∧-intro
              (
              atp-conjunct $
                atp-canonicalize $
                  atp-strip $
                    assume {Γ = Γ} $
                      atp-neg subgoal₃
              )
              (
              atp-conjunct $
                atp-canonicalize $
                  atp-strip $
                    assume {Γ = Γ} $
                      atp-neg subgoal₃
              )
          )

proof₄ : Γ ⊢ subgoal₄
proof₄ =
  RAA $
  -- Γ , ¬ subgoal₄⊢ ⊥
    atp-canonicalize $
      atp-simplify $
        ∧-intro
          (
          atp-conjunct $
            atp-canonicalize $
              atp-strip $
                assume {Γ = Γ} $
                  atp-neg subgoal₄
          )
          (
          ∧-intro
            (
            atp-conjunct $
              atp-canonicalize $
                atp-strip $
                  assume {Γ = Γ} $
                    atp-neg subgoal₄
            )
            (
            ∧-intro
              (
              atp-conjunct $
                atp-canonicalize $
                  atp-strip $
                    assume {Γ = Γ} $
                      atp-neg subgoal₄
              )
              (
              atp-conjunct $
                atp-canonicalize $
                  atp-strip $
                    assume {Γ = Γ} $
                      atp-neg subgoal₄
              )
            )
          )

proof₅ : Γ ⊢ subgoal₅
proof₅ =
  RAA $
  -- Γ , ¬ subgoal₅⊢ ⊥
    atp-canonicalize $
      atp-simplify $
        ∧-intro
          (
          atp-conjunct $
            atp-canonicalize $
              atp-strip $
                assume {Γ = Γ} $
                  atp-neg subgoal₅
          )
          (
          ∧-intro
            (
            atp-conjunct $
              atp-canonicalize $
                atp-strip $
                  assume {Γ = Γ} $
                    atp-neg subgoal₅
            )
            (
            ∧-intro
              (
              atp-conjunct $
                atp-canonicalize $
                  atp-strip $
                    assume {Γ = Γ} $
                      atp-neg subgoal₅
              )
              (
              atp-conjunct $
                atp-canonicalize $
                  atp-strip $
                    assume {Γ = Γ} $
                      atp-neg subgoal₅
              )
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
          (
          ∧-intro
            subgoal₃
            (
            ∧-intro
              subgoal₄
              subgoal₅
            )
          )
        )
      )
    )

