
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
    atp-canonicalize $  -- Γ ⊢ ⊥
      atp-simplify $  -- Γ ⊢ ⊥
        ∧-intro
          (
          ∧-proj₂ $ -- ((¬ p ⇔ (¬ q ⇔ ¬ r)) ≟ (¬ p ⇔ (¬ q ⇔ ¬ r)))
            atp-canonicalize $  -- Γ ⊢ (((¬ r ∧ p) ∧ q) ∧ (¬ p ⇔ (¬ q ⇔ ¬ r)))
              atp-strip $  -- Γ ⊢ (((((p ⇔ q) ⇔ r) ∧ p) ∧ q) ⇒ r)
                assume {Γ = Γ} $  -- Γ ⊢ ¬ (((((p ⇔ q) ⇔ r) ∧ p) ∧ q) ⇒ r)
                  atp-neg subgoal₀
          )
          (
          ∧-intro
            (
            ∧-proj₁ $ -- 1: ((¬ r ∧ p) ∧ q)
              atp-canonicalize $  -- Γ ⊢ (((¬ r ∧ p) ∧ q) ∧ (¬ p ⇔ (¬ q ⇔ ¬ r)))
                atp-strip $  -- Γ ⊢ (((((p ⇔ q) ⇔ r) ∧ p) ∧ q) ⇒ r)
                  assume {Γ = Γ} $  -- Γ ⊢ ¬ (((((p ⇔ q) ⇔ r) ∧ p) ∧ q) ⇒ r)
                    atp-neg subgoal₀
            )
            (
            ∧-intro
              (
              ∧-proj₁ $ -- 1: ((¬ r ∧ p) ∧ q)
                atp-canonicalize $  -- Γ ⊢ (((¬ r ∧ p) ∧ q) ∧ (¬ p ⇔ (¬ q ⇔ ¬ r)))
                  atp-strip $  -- Γ ⊢ (((((p ⇔ q) ⇔ r) ∧ p) ∧ q) ⇒ r)
                    assume {Γ = Γ} $  -- Γ ⊢ ¬ (((((p ⇔ q) ⇔ r) ∧ p) ∧ q) ⇒ r)
                      atp-neg subgoal₀
              )
              (
              ∧-proj₁ $ -- 1: ((¬ r ∧ p) ∧ q)
                atp-canonicalize $  -- Γ ⊢ (((¬ r ∧ p) ∧ q) ∧ (¬ p ⇔ (¬ q ⇔ ¬ r)))
                  atp-strip $  -- Γ ⊢ (((((p ⇔ q) ⇔ r) ∧ p) ∧ q) ⇒ r)
                    assume {Γ = Γ} $  -- Γ ⊢ ¬ (((((p ⇔ q) ⇔ r) ∧ p) ∧ q) ⇒ r)
                      atp-neg subgoal₀
              )
            )
          )

proof₁ : Γ ⊢ subgoal₁
proof₁ =
  RAA $
    atp-canonicalize $  -- Γ ⊢ ⊥
      atp-simplify $  -- Γ ⊢ ⊥
        ∧-intro
          (
          ∧-proj₂ $ -- ((¬ p ⇔ (¬ q ⇔ ¬ r)) ≟ (¬ p ⇔ (¬ q ⇔ ¬ r)))
            atp-canonicalize $  -- Γ ⊢ (((¬ q ∧ p) ∧ r) ∧ (¬ p ⇔ (¬ q ⇔ ¬ r)))
              atp-strip $  -- Γ ⊢ (((((p ⇔ q) ⇔ r) ∧ p) ∧ r) ⇒ q)
                assume {Γ = Γ} $  -- Γ ⊢ ¬ (((((p ⇔ q) ⇔ r) ∧ p) ∧ r) ⇒ q)
                  atp-neg subgoal₁
          )
          (
          ∧-intro
            (
            ∧-proj₁ $ -- 1: ((¬ q ∧ p) ∧ r)
              atp-canonicalize $  -- Γ ⊢ (((¬ q ∧ p) ∧ r) ∧ (¬ p ⇔ (¬ q ⇔ ¬ r)))
                atp-strip $  -- Γ ⊢ (((((p ⇔ q) ⇔ r) ∧ p) ∧ r) ⇒ q)
                  assume {Γ = Γ} $  -- Γ ⊢ ¬ (((((p ⇔ q) ⇔ r) ∧ p) ∧ r) ⇒ q)
                    atp-neg subgoal₁
            )
            (
            ∧-intro
              (
              ∧-proj₁ $ -- 1: ((¬ q ∧ p) ∧ r)
                atp-canonicalize $  -- Γ ⊢ (((¬ q ∧ p) ∧ r) ∧ (¬ p ⇔ (¬ q ⇔ ¬ r)))
                  atp-strip $  -- Γ ⊢ (((((p ⇔ q) ⇔ r) ∧ p) ∧ r) ⇒ q)
                    assume {Γ = Γ} $  -- Γ ⊢ ¬ (((((p ⇔ q) ⇔ r) ∧ p) ∧ r) ⇒ q)
                      atp-neg subgoal₁
              )
              (
              ∧-proj₁ $ -- 1: ((¬ q ∧ p) ∧ r)
                atp-canonicalize $  -- Γ ⊢ (((¬ q ∧ p) ∧ r) ∧ (¬ p ⇔ (¬ q ⇔ ¬ r)))
                  atp-strip $  -- Γ ⊢ (((((p ⇔ q) ⇔ r) ∧ p) ∧ r) ⇒ q)
                    assume {Γ = Γ} $  -- Γ ⊢ ¬ (((((p ⇔ q) ⇔ r) ∧ p) ∧ r) ⇒ q)
                      atp-neg subgoal₁
              )
            )
          )

proof₂ : Γ ⊢ subgoal₂
proof₂ =
  RAA $
    atp-canonicalize $  -- Γ ⊢ ⊥
      atp-simplify $  -- Γ ⊢ ⊥
        ∧-intro
          (
          ∧-proj₂ $ -- ((¬ p ⇔ (¬ q ⇔ ¬ r)) ≟ (¬ p ⇔ (¬ q ⇔ ¬ r)))
            atp-canonicalize $  -- Γ ⊢ ((¬ p ∧ (¬ q ⇔ ¬ r)) ∧ (¬ p ⇔ (¬ q ⇔ ¬ r)))
              atp-strip $  -- Γ ⊢ ((((p ⇔ q) ⇔ r) ∧ (q ⇔ r)) ⇒ p)
                assume {Γ = Γ} $  -- Γ ⊢ ¬ ((((p ⇔ q) ⇔ r) ∧ (q ⇔ r)) ⇒ p)
                  atp-neg subgoal₂
          )
          (
          ∧-intro
            (
            ∧-proj₁ $ -- 1: (¬ p ∧ (¬ q ⇔ ¬ r))
              atp-canonicalize $  -- Γ ⊢ ((¬ p ∧ (¬ q ⇔ ¬ r)) ∧ (¬ p ⇔ (¬ q ⇔ ¬ r)))
                atp-strip $  -- Γ ⊢ ((((p ⇔ q) ⇔ r) ∧ (q ⇔ r)) ⇒ p)
                  assume {Γ = Γ} $  -- Γ ⊢ ¬ ((((p ⇔ q) ⇔ r) ∧ (q ⇔ r)) ⇒ p)
                    atp-neg subgoal₂
            )
            (
            ∧-proj₁ $ -- 1: (¬ p ∧ (¬ q ⇔ ¬ r))
              atp-canonicalize $  -- Γ ⊢ ((¬ p ∧ (¬ q ⇔ ¬ r)) ∧ (¬ p ⇔ (¬ q ⇔ ¬ r)))
                atp-strip $  -- Γ ⊢ ((((p ⇔ q) ⇔ r) ∧ (q ⇔ r)) ⇒ p)
                  assume {Γ = Γ} $  -- Γ ⊢ ¬ ((((p ⇔ q) ⇔ r) ∧ (q ⇔ r)) ⇒ p)
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
          ∧-proj₂ $ -- ((¬ p ⇔ (¬ q ⇔ ¬ r)) ≟ (¬ p ⇔ (¬ q ⇔ ¬ r)))
            atp-canonicalize $  -- Γ ⊢ ((¬ r ∧ (¬ p ⇔ ¬ q)) ∧ (¬ p ⇔ (¬ q ⇔ ¬ r)))
              atp-strip $  -- Γ ⊢ (((p ⇔ (q ⇔ r)) ∧ (p ⇔ q)) ⇒ r)
                assume {Γ = Γ} $  -- Γ ⊢ ¬ (((p ⇔ (q ⇔ r)) ∧ (p ⇔ q)) ⇒ r)
                  atp-neg subgoal₃
          )
          (
          ∧-intro
            (
            ∧-proj₁ $ -- 1: (¬ r ∧ (¬ p ⇔ ¬ q))
              atp-canonicalize $  -- Γ ⊢ ((¬ r ∧ (¬ p ⇔ ¬ q)) ∧ (¬ p ⇔ (¬ q ⇔ ¬ r)))
                atp-strip $  -- Γ ⊢ (((p ⇔ (q ⇔ r)) ∧ (p ⇔ q)) ⇒ r)
                  assume {Γ = Γ} $  -- Γ ⊢ ¬ (((p ⇔ (q ⇔ r)) ∧ (p ⇔ q)) ⇒ r)
                    atp-neg subgoal₃
            )
            (
            ∧-proj₁ $ -- 1: (¬ r ∧ (¬ p ⇔ ¬ q))
              atp-canonicalize $  -- Γ ⊢ ((¬ r ∧ (¬ p ⇔ ¬ q)) ∧ (¬ p ⇔ (¬ q ⇔ ¬ r)))
                atp-strip $  -- Γ ⊢ (((p ⇔ (q ⇔ r)) ∧ (p ⇔ q)) ⇒ r)
                  assume {Γ = Γ} $  -- Γ ⊢ ¬ (((p ⇔ (q ⇔ r)) ∧ (p ⇔ q)) ⇒ r)
                    atp-neg subgoal₃
            )
          )

proof₄ : Γ ⊢ subgoal₄
proof₄ =
  RAA $
    atp-canonicalize $  -- Γ ⊢ ⊥
      atp-simplify $  -- Γ ⊢ ⊥
        ∧-intro
          (
          ∧-proj₂ $ -- ((¬ p ⇔ (¬ q ⇔ ¬ r)) ≟ (¬ p ⇔ (¬ q ⇔ ¬ r)))
            atp-canonicalize $  -- Γ ⊢ (((¬ q ∧ p) ∧ r) ∧ (¬ p ⇔ (¬ q ⇔ ¬ r)))
              atp-strip $  -- Γ ⊢ ((((p ⇔ (q ⇔ r)) ∧ r) ∧ p) ⇒ q)
                assume {Γ = Γ} $  -- Γ ⊢ ¬ ((((p ⇔ (q ⇔ r)) ∧ r) ∧ p) ⇒ q)
                  atp-neg subgoal₄
          )
          (
          ∧-intro
            (
            ∧-proj₁ $ -- 1: ((¬ q ∧ p) ∧ r)
              atp-canonicalize $  -- Γ ⊢ (((¬ q ∧ p) ∧ r) ∧ (¬ p ⇔ (¬ q ⇔ ¬ r)))
                atp-strip $  -- Γ ⊢ ((((p ⇔ (q ⇔ r)) ∧ r) ∧ p) ⇒ q)
                  assume {Γ = Γ} $  -- Γ ⊢ ¬ ((((p ⇔ (q ⇔ r)) ∧ r) ∧ p) ⇒ q)
                    atp-neg subgoal₄
            )
            (
            ∧-intro
              (
              ∧-proj₁ $ -- 1: ((¬ q ∧ p) ∧ r)
                atp-canonicalize $  -- Γ ⊢ (((¬ q ∧ p) ∧ r) ∧ (¬ p ⇔ (¬ q ⇔ ¬ r)))
                  atp-strip $  -- Γ ⊢ ((((p ⇔ (q ⇔ r)) ∧ r) ∧ p) ⇒ q)
                    assume {Γ = Γ} $  -- Γ ⊢ ¬ ((((p ⇔ (q ⇔ r)) ∧ r) ∧ p) ⇒ q)
                      atp-neg subgoal₄
              )
              (
              ∧-proj₁ $ -- 1: ((¬ q ∧ p) ∧ r)
                atp-canonicalize $  -- Γ ⊢ (((¬ q ∧ p) ∧ r) ∧ (¬ p ⇔ (¬ q ⇔ ¬ r)))
                  atp-strip $  -- Γ ⊢ ((((p ⇔ (q ⇔ r)) ∧ r) ∧ p) ⇒ q)
                    assume {Γ = Γ} $  -- Γ ⊢ ¬ ((((p ⇔ (q ⇔ r)) ∧ r) ∧ p) ⇒ q)
                      atp-neg subgoal₄
              )
            )
          )

proof₅ : Γ ⊢ subgoal₅
proof₅ =
  RAA $
    atp-canonicalize $  -- Γ ⊢ ⊥
      atp-simplify $  -- Γ ⊢ ⊥
        ∧-intro
          (
          ∧-proj₂ $ -- ((¬ p ⇔ (¬ q ⇔ ¬ r)) ≟ (¬ p ⇔ (¬ q ⇔ ¬ r)))
            atp-canonicalize $  -- Γ ⊢ (((¬ p ∧ q) ∧ r) ∧ (¬ p ⇔ (¬ q ⇔ ¬ r)))
              atp-strip $  -- Γ ⊢ ((((p ⇔ (q ⇔ r)) ∧ r) ∧ q) ⇒ p)
                assume {Γ = Γ} $  -- Γ ⊢ ¬ ((((p ⇔ (q ⇔ r)) ∧ r) ∧ q) ⇒ p)
                  atp-neg subgoal₅
          )
          (
          ∧-intro
            (
            ∧-proj₁ $ -- 1: ((¬ p ∧ q) ∧ r)
              atp-canonicalize $  -- Γ ⊢ (((¬ p ∧ q) ∧ r) ∧ (¬ p ⇔ (¬ q ⇔ ¬ r)))
                atp-strip $  -- Γ ⊢ ((((p ⇔ (q ⇔ r)) ∧ r) ∧ q) ⇒ p)
                  assume {Γ = Γ} $  -- Γ ⊢ ¬ ((((p ⇔ (q ⇔ r)) ∧ r) ∧ q) ⇒ p)
                    atp-neg subgoal₅
            )
            (
            ∧-intro
              (
              ∧-proj₁ $ -- 1: ((¬ p ∧ q) ∧ r)
                atp-canonicalize $  -- Γ ⊢ (((¬ p ∧ q) ∧ r) ∧ (¬ p ⇔ (¬ q ⇔ ¬ r)))
                  atp-strip $  -- Γ ⊢ ((((p ⇔ (q ⇔ r)) ∧ r) ∧ q) ⇒ p)
                    assume {Γ = Γ} $  -- Γ ⊢ ¬ ((((p ⇔ (q ⇔ r)) ∧ r) ∧ q) ⇒ p)
                      atp-neg subgoal₅
              )
              (
              ∧-proj₁ $ -- 1: ((¬ p ∧ q) ∧ r)
                atp-canonicalize $  -- Γ ⊢ (((¬ p ∧ q) ∧ r) ∧ (¬ p ⇔ (¬ q ⇔ ¬ r)))
                  atp-strip $  -- Γ ⊢ ((((p ⇔ (q ⇔ r)) ∧ r) ∧ q) ⇒ p)
                    assume {Γ = Γ} $  -- Γ ⊢ ¬ ((((p ⇔ (q ⇔ r)) ∧ r) ∧ q) ⇒ p)
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

