
-- tstp2agda proof

open import Data.FOL.Deep 8 public
open import Data.FOL.Deep.ATP.Metis 8 public

-- Vars
a : Prop
a = Var (# 0)

b : Prop
b = Var (# 1)

c : Prop
c = Var (# 2)

d : Prop
d = Var (# 3)

e : Prop
e = Var (# 4)

f : Prop
f = Var (# 5)

g : Prop
g = Var (# 6)

h : Prop
h = Var (# 7)

-- Premise
Γ : Ctxt
Γ = ∅

-- Conjecture
goal : Prop
goal = (((((((((¬ a ∧ (a ∨ b)) ∧ (c ∨ d)) ∧ ((¬ b ∨ e) ∨ f)) ∧ (¬ c ∨ ¬ e)) ∧ (¬ c ∨ ¬ f)) ∧ ((¬ b ∨ g) ∨ h)) ∧ (¬ d ∨ ¬ g)) ∧ (¬ d ∨ ¬ h)) ⇒ ⊥)


-- Subgoal
subgoal₀ : Prop
subgoal₀ = (((((((((¬ a ∧ (a ∨ b)) ∧ (c ∨ d)) ∧ ((¬ b ∨ e) ∨ f)) ∧ (¬ c ∨ ¬ e)) ∧ (¬ c ∨ ¬ f)) ∧ ((¬ b ∨ g) ∨ h)) ∧ (¬ d ∨ ¬ g)) ∧ (¬ d ∨ ¬ h)) ⇒ ⊥)

-- Metis Proof.
proof₀ : Γ ⊢ subgoal₀
proof₀ =
  RAA $
    atp-canonicalize $  -- Γ ⊢ ({ c e : Set} → ¬ c ∨ ¬ e)
      ∧-proj₁ $ -- 1: (((((((¬ a ∧ (¬ c ∨ ¬ e)) ∧ (¬ c ∨ ¬ f)) ∧ (¬ d ∨ ¬ g)) ∧ (¬ d ∨ ¬ h)) ∧ (a ∨ b)) ∧ (c ∨ d)) ∧ ((¬ b ∨ e) ∨ f))
        atp-canonicalize $  -- Γ ⊢ ((((((((¬ a ∧ (¬ c ∨ ¬ e)) ∧ (¬ c ∨ ¬ f)) ∧ (¬ d ∨ ¬ g)) ∧ (¬ d ∨ ¬ h)) ∧ (a ∨ b)) ∧ (c ∨ d)) ∧ ((¬ b ∨ e) ∨ f)) ∧ ((¬ b ∨ g) ∨ h))
          atp-strip $  -- Γ ⊢ (((((((((¬ a ∧ (a ∨ b)) ∧ (c ∨ d)) ∧ ((¬ b ∨ e) ∨ f)) ∧ (¬ c ∨ ¬ e)) ∧ (¬ c ∨ ¬ f)) ∧ ((¬ b ∨ g) ∨ h)) ∧ (¬ d ∨ ¬ g)) ∧ (¬ d ∨ ¬ h)) ⇒ ⊥)
            assume {Γ = Γ} $  -- Γ ⊢ ¬ (((((((((¬ a ∧ (a ∨ b)) ∧ (c ∨ d)) ∧ ((¬ b ∨ e) ∨ f)) ∧ (¬ c ∨ ¬ e)) ∧ (¬ c ∨ ¬ f)) ∧ ((¬ b ∨ g) ∨ h)) ∧ (¬ d ∨ ¬ g)) ∧ (¬ d ∨ ¬ h)) ⇒ ⊥)
              atp-neg subgoal₀

proof₁ : Γ ⊢ subgoal₁
proof₁ =
  RAA $
    atp-canonicalize $  -- Γ ⊢ ({ c f : Set} → ¬ c ∨ ¬ f)
      ∧-proj₁ $ -- 1: (((((((¬ a ∧ (¬ c ∨ ¬ e)) ∧ (¬ c ∨ ¬ f)) ∧ (¬ d ∨ ¬ g)) ∧ (¬ d ∨ ¬ h)) ∧ (a ∨ b)) ∧ (c ∨ d)) ∧ ((¬ b ∨ e) ∨ f))
        atp-canonicalize $  -- Γ ⊢ ((((((((¬ a ∧ (¬ c ∨ ¬ e)) ∧ (¬ c ∨ ¬ f)) ∧ (¬ d ∨ ¬ g)) ∧ (¬ d ∨ ¬ h)) ∧ (a ∨ b)) ∧ (c ∨ d)) ∧ ((¬ b ∨ e) ∨ f)) ∧ ((¬ b ∨ g) ∨ h))
          atp-strip $  -- Γ ⊢ (((((((((¬ a ∧ (a ∨ b)) ∧ (c ∨ d)) ∧ ((¬ b ∨ e) ∨ f)) ∧ (¬ c ∨ ¬ e)) ∧ (¬ c ∨ ¬ f)) ∧ ((¬ b ∨ g) ∨ h)) ∧ (¬ d ∨ ¬ g)) ∧ (¬ d ∨ ¬ h)) ⇒ ⊥)
            assume {Γ = Γ} $  -- Γ ⊢ ¬ (((((((((¬ a ∧ (a ∨ b)) ∧ (c ∨ d)) ∧ ((¬ b ∨ e) ∨ f)) ∧ (¬ c ∨ ¬ e)) ∧ (¬ c ∨ ¬ f)) ∧ ((¬ b ∨ g) ∨ h)) ∧ (¬ d ∨ ¬ g)) ∧ (¬ d ∨ ¬ h)) ⇒ ⊥)
              atp-neg subgoal₁

proof₂ : Γ ⊢ subgoal₂
proof₂ =
  RAA $
    atp-canonicalize $  -- Γ ⊢ ({ e f : Set} → e ∨ f)
      atp-simplify $  -- Γ ⊢ (e ∨ f)
        ∧-intro
          (
          ∧-proj₁ $ -- 1: (((((((¬ a ∧ (¬ c ∨ ¬ e)) ∧ (¬ c ∨ ¬ f)) ∧ (¬ d ∨ ¬ g)) ∧ (¬ d ∨ ¬ h)) ∧ (a ∨ b)) ∧ (c ∨ d)) ∧ ((¬ b ∨ e) ∨ f))
            atp-canonicalize $  -- Γ ⊢ ((((((((¬ a ∧ (¬ c ∨ ¬ e)) ∧ (¬ c ∨ ¬ f)) ∧ (¬ d ∨ ¬ g)) ∧ (¬ d ∨ ¬ h)) ∧ (a ∨ b)) ∧ (c ∨ d)) ∧ ((¬ b ∨ e) ∨ f)) ∧ ((¬ b ∨ g) ∨ h))
              atp-strip $  -- Γ ⊢ (((((((((¬ a ∧ (a ∨ b)) ∧ (c ∨ d)) ∧ ((¬ b ∨ e) ∨ f)) ∧ (¬ c ∨ ¬ e)) ∧ (¬ c ∨ ¬ f)) ∧ ((¬ b ∨ g) ∨ h)) ∧ (¬ d ∨ ¬ g)) ∧ (¬ d ∨ ¬ h)) ⇒ ⊥)
                assume {Γ = Γ} $  -- Γ ⊢ ¬ (((((((((¬ a ∧ (a ∨ b)) ∧ (c ∨ d)) ∧ ((¬ b ∨ e) ∨ f)) ∧ (¬ c ∨ ¬ e)) ∧ (¬ c ∨ ¬ f)) ∧ ((¬ b ∨ g) ∨ h)) ∧ (¬ d ∨ ¬ g)) ∧ (¬ d ∨ ¬ h)) ⇒ ⊥)
                  atp-neg subgoal₂
          )
          (
          atp-simplify $  -- Γ ⊢ b
            ∧-intro
              (
              ∧-proj₁ $ -- 1: (((((((¬ a ∧ (¬ c ∨ ¬ e)) ∧ (¬ c ∨ ¬ f)) ∧ (¬ d ∨ ¬ g)) ∧ (¬ d ∨ ¬ h)) ∧ (a ∨ b)) ∧ (c ∨ d)) ∧ ((¬ b ∨ e) ∨ f))
                atp-canonicalize $  -- Γ ⊢ ((((((((¬ a ∧ (¬ c ∨ ¬ e)) ∧ (¬ c ∨ ¬ f)) ∧ (¬ d ∨ ¬ g)) ∧ (¬ d ∨ ¬ h)) ∧ (a ∨ b)) ∧ (c ∨ d)) ∧ ((¬ b ∨ e) ∨ f)) ∧ ((¬ b ∨ g) ∨ h))
                  atp-strip $  -- Γ ⊢ (((((((((¬ a ∧ (a ∨ b)) ∧ (c ∨ d)) ∧ ((¬ b ∨ e) ∨ f)) ∧ (¬ c ∨ ¬ e)) ∧ (¬ c ∨ ¬ f)) ∧ ((¬ b ∨ g) ∨ h)) ∧ (¬ d ∨ ¬ g)) ∧ (¬ d ∨ ¬ h)) ⇒ ⊥)
                    assume {Γ = Γ} $  -- Γ ⊢ ¬ (((((((((¬ a ∧ (a ∨ b)) ∧ (c ∨ d)) ∧ ((¬ b ∨ e) ∨ f)) ∧ (¬ c ∨ ¬ e)) ∧ (¬ c ∨ ¬ f)) ∧ ((¬ b ∨ g) ∨ h)) ∧ (¬ d ∨ ¬ g)) ∧ (¬ d ∨ ¬ h)) ⇒ ⊥)
                      atp-neg subgoal₂
              )
              (
              ∧-proj₁ $ -- 1: (((((((¬ a ∧ (¬ c ∨ ¬ e)) ∧ (¬ c ∨ ¬ f)) ∧ (¬ d ∨ ¬ g)) ∧ (¬ d ∨ ¬ h)) ∧ (a ∨ b)) ∧ (c ∨ d)) ∧ ((¬ b ∨ e) ∨ f))
                atp-canonicalize $  -- Γ ⊢ ((((((((¬ a ∧ (¬ c ∨ ¬ e)) ∧ (¬ c ∨ ¬ f)) ∧ (¬ d ∨ ¬ g)) ∧ (¬ d ∨ ¬ h)) ∧ (a ∨ b)) ∧ (c ∨ d)) ∧ ((¬ b ∨ e) ∨ f)) ∧ ((¬ b ∨ g) ∨ h))
                  atp-strip $  -- Γ ⊢ (((((((((¬ a ∧ (a ∨ b)) ∧ (c ∨ d)) ∧ ((¬ b ∨ e) ∨ f)) ∧ (¬ c ∨ ¬ e)) ∧ (¬ c ∨ ¬ f)) ∧ ((¬ b ∨ g) ∨ h)) ∧ (¬ d ∨ ¬ g)) ∧ (¬ d ∨ ¬ h)) ⇒ ⊥)
                    assume {Γ = Γ} $  -- Γ ⊢ ¬ (((((((((¬ a ∧ (a ∨ b)) ∧ (c ∨ d)) ∧ ((¬ b ∨ e) ∨ f)) ∧ (¬ c ∨ ¬ e)) ∧ (¬ c ∨ ¬ f)) ∧ ((¬ b ∨ g) ∨ h)) ∧ (¬ d ∨ ¬ g)) ∧ (¬ d ∨ ¬ h)) ⇒ ⊥)
                      atp-neg subgoal₂
              )
          )

proof₃ : Γ ⊢ subgoal₃
proof₃ =
  RAA $
    id -- resolve 4.
      (
              atp-canonicalize $  -- Γ ⊢ ({ e f : Set} → e ∨ f)
          atp-simplify $  -- Γ ⊢ (e ∨ f)
            ∧-intro
              (
              ∧-proj₁ $ -- 1: (((((((¬ a ∧ (¬ c ∨ ¬ e)) ∧ (¬ c ∨ ¬ f)) ∧ (¬ d ∨ ¬ g)) ∧ (¬ d ∨ ¬ h)) ∧ (a ∨ b)) ∧ (c ∨ d)) ∧ ((¬ b ∨ e) ∨ f))
                atp-canonicalize $  -- Γ ⊢ ((((((((¬ a ∧ (¬ c ∨ ¬ e)) ∧ (¬ c ∨ ¬ f)) ∧ (¬ d ∨ ¬ g)) ∧ (¬ d ∨ ¬ h)) ∧ (a ∨ b)) ∧ (c ∨ d)) ∧ ((¬ b ∨ e) ∨ f)) ∧ ((¬ b ∨ g) ∨ h))
                  atp-strip $  -- Γ ⊢ (((((((((¬ a ∧ (a ∨ b)) ∧ (c ∨ d)) ∧ ((¬ b ∨ e) ∨ f)) ∧ (¬ c ∨ ¬ e)) ∧ (¬ c ∨ ¬ f)) ∧ ((¬ b ∨ g) ∨ h)) ∧ (¬ d ∨ ¬ g)) ∧ (¬ d ∨ ¬ h)) ⇒ ⊥)
                    assume {Γ = Γ} $  -- Γ ⊢ ¬ (((((((((¬ a ∧ (a ∨ b)) ∧ (c ∨ d)) ∧ ((¬ b ∨ e) ∨ f)) ∧ (¬ c ∨ ¬ e)) ∧ (¬ c ∨ ¬ f)) ∧ ((¬ b ∨ g) ∨ h)) ∧ (¬ d ∨ ¬ g)) ∧ (¬ d ∨ ¬ h)) ⇒ ⊥)
                      atp-neg subgoal₃
              )
              (
              atp-simplify $  -- Γ ⊢ b
                ∧-intro
                  (
                  ∧-proj₁ $ -- 1: (((((((¬ a ∧ (¬ c ∨ ¬ e)) ∧ (¬ c ∨ ¬ f)) ∧ (¬ d ∨ ¬ g)) ∧ (¬ d ∨ ¬ h)) ∧ (a ∨ b)) ∧ (c ∨ d)) ∧ ((¬ b ∨ e) ∨ f))
                    atp-canonicalize $  -- Γ ⊢ ((((((((¬ a ∧ (¬ c ∨ ¬ e)) ∧ (¬ c ∨ ¬ f)) ∧ (¬ d ∨ ¬ g)) ∧ (¬ d ∨ ¬ h)) ∧ (a ∨ b)) ∧ (c ∨ d)) ∧ ((¬ b ∨ e) ∨ f)) ∧ ((¬ b ∨ g) ∨ h))
                      atp-strip $  -- Γ ⊢ (((((((((¬ a ∧ (a ∨ b)) ∧ (c ∨ d)) ∧ ((¬ b ∨ e) ∨ f)) ∧ (¬ c ∨ ¬ e)) ∧ (¬ c ∨ ¬ f)) ∧ ((¬ b ∨ g) ∨ h)) ∧ (¬ d ∨ ¬ g)) ∧ (¬ d ∨ ¬ h)) ⇒ ⊥)
                        assume {Γ = Γ} $  -- Γ ⊢ ¬ (((((((((¬ a ∧ (a ∨ b)) ∧ (c ∨ d)) ∧ ((¬ b ∨ e) ∨ f)) ∧ (¬ c ∨ ¬ e)) ∧ (¬ c ∨ ¬ f)) ∧ ((¬ b ∨ g) ∨ h)) ∧ (¬ d ∨ ¬ g)) ∧ (¬ d ∨ ¬ h)) ⇒ ⊥)
                          atp-neg subgoal₃
                  )
                  (
                  ∧-proj₁ $ -- 1: (((((((¬ a ∧ (¬ c ∨ ¬ e)) ∧ (¬ c ∨ ¬ f)) ∧ (¬ d ∨ ¬ g)) ∧ (¬ d ∨ ¬ h)) ∧ (a ∨ b)) ∧ (c ∨ d)) ∧ ((¬ b ∨ e) ∨ f))
                    atp-canonicalize $  -- Γ ⊢ ((((((((¬ a ∧ (¬ c ∨ ¬ e)) ∧ (¬ c ∨ ¬ f)) ∧ (¬ d ∨ ¬ g)) ∧ (¬ d ∨ ¬ h)) ∧ (a ∨ b)) ∧ (c ∨ d)) ∧ ((¬ b ∨ e) ∨ f)) ∧ ((¬ b ∨ g) ∨ h))
                      atp-strip $  -- Γ ⊢ (((((((((¬ a ∧ (a ∨ b)) ∧ (c ∨ d)) ∧ ((¬ b ∨ e) ∨ f)) ∧ (¬ c ∨ ¬ e)) ∧ (¬ c ∨ ¬ f)) ∧ ((¬ b ∨ g) ∨ h)) ∧ (¬ d ∨ ¬ g)) ∧ (¬ d ∨ ¬ h)) ⇒ ⊥)
                        assume {Γ = Γ} $  -- Γ ⊢ ¬ (((((((((¬ a ∧ (a ∨ b)) ∧ (c ∨ d)) ∧ ((¬ b ∨ e) ∨ f)) ∧ (¬ c ∨ ¬ e)) ∧ (¬ c ∨ ¬ f)) ∧ ((¬ b ∨ g) ∨ h)) ∧ (¬ d ∨ ¬ g)) ∧ (¬ d ∨ ¬ h)) ⇒ ⊥)
                          atp-neg subgoal₃
                  )
              )
      )
      (
              atp-canonicalize $  -- Γ ⊢ ({ c f : Set} → ¬ c ∨ ¬ f)
          ∧-proj₁ $ -- 1: (((((((¬ a ∧ (¬ c ∨ ¬ e)) ∧ (¬ c ∨ ¬ f)) ∧ (¬ d ∨ ¬ g)) ∧ (¬ d ∨ ¬ h)) ∧ (a ∨ b)) ∧ (c ∨ d)) ∧ ((¬ b ∨ e) ∨ f))
            atp-canonicalize $  -- Γ ⊢ ((((((((¬ a ∧ (¬ c ∨ ¬ e)) ∧ (¬ c ∨ ¬ f)) ∧ (¬ d ∨ ¬ g)) ∧ (¬ d ∨ ¬ h)) ∧ (a ∨ b)) ∧ (c ∨ d)) ∧ ((¬ b ∨ e) ∨ f)) ∧ ((¬ b ∨ g) ∨ h))
              atp-strip $  -- Γ ⊢ (((((((((¬ a ∧ (a ∨ b)) ∧ (c ∨ d)) ∧ ((¬ b ∨ e) ∨ f)) ∧ (¬ c ∨ ¬ e)) ∧ (¬ c ∨ ¬ f)) ∧ ((¬ b ∨ g) ∨ h)) ∧ (¬ d ∨ ¬ g)) ∧ (¬ d ∨ ¬ h)) ⇒ ⊥)
                assume {Γ = Γ} $  -- Γ ⊢ ¬ (((((((((¬ a ∧ (a ∨ b)) ∧ (c ∨ d)) ∧ ((¬ b ∨ e) ∨ f)) ∧ (¬ c ∨ ¬ e)) ∧ (¬ c ∨ ¬ f)) ∧ ((¬ b ∨ g) ∨ h)) ∧ (¬ d ∨ ¬ g)) ∧ (¬ d ∨ ¬ h)) ⇒ ⊥)
                  atp-neg subgoal₃
      )

proof₄ : Γ ⊢ subgoal₄
proof₄ =
  RAA $
    atp-canonicalize $  -- Γ ⊢ ({ c d : Set} → c ∨ d)
      ∧-proj₁ $ -- 1: (((((((¬ a ∧ (¬ c ∨ ¬ e)) ∧ (¬ c ∨ ¬ f)) ∧ (¬ d ∨ ¬ g)) ∧ (¬ d ∨ ¬ h)) ∧ (a ∨ b)) ∧ (c ∨ d)) ∧ ((¬ b ∨ e) ∨ f))
        atp-canonicalize $  -- Γ ⊢ ((((((((¬ a ∧ (¬ c ∨ ¬ e)) ∧ (¬ c ∨ ¬ f)) ∧ (¬ d ∨ ¬ g)) ∧ (¬ d ∨ ¬ h)) ∧ (a ∨ b)) ∧ (c ∨ d)) ∧ ((¬ b ∨ e) ∨ f)) ∧ ((¬ b ∨ g) ∨ h))
          atp-strip $  -- Γ ⊢ (((((((((¬ a ∧ (a ∨ b)) ∧ (c ∨ d)) ∧ ((¬ b ∨ e) ∨ f)) ∧ (¬ c ∨ ¬ e)) ∧ (¬ c ∨ ¬ f)) ∧ ((¬ b ∨ g) ∨ h)) ∧ (¬ d ∨ ¬ g)) ∧ (¬ d ∨ ¬ h)) ⇒ ⊥)
            assume {Γ = Γ} $  -- Γ ⊢ ¬ (((((((((¬ a ∧ (a ∨ b)) ∧ (c ∨ d)) ∧ ((¬ b ∨ e) ∨ f)) ∧ (¬ c ∨ ¬ e)) ∧ (¬ c ∨ ¬ f)) ∧ ((¬ b ∨ g) ∨ h)) ∧ (¬ d ∨ ¬ g)) ∧ (¬ d ∨ ¬ h)) ⇒ ⊥)
              atp-neg subgoal₄

proof₅ : Γ ⊢ subgoal₅
proof₅ =
  RAA $
    atp-canonicalize $  -- Γ ⊢ ({ d g : Set} → ¬ d ∨ ¬ g)
      ∧-proj₁ $ -- 1: (((((((¬ a ∧ (¬ c ∨ ¬ e)) ∧ (¬ c ∨ ¬ f)) ∧ (¬ d ∨ ¬ g)) ∧ (¬ d ∨ ¬ h)) ∧ (a ∨ b)) ∧ (c ∨ d)) ∧ ((¬ b ∨ e) ∨ f))
        atp-canonicalize $  -- Γ ⊢ ((((((((¬ a ∧ (¬ c ∨ ¬ e)) ∧ (¬ c ∨ ¬ f)) ∧ (¬ d ∨ ¬ g)) ∧ (¬ d ∨ ¬ h)) ∧ (a ∨ b)) ∧ (c ∨ d)) ∧ ((¬ b ∨ e) ∨ f)) ∧ ((¬ b ∨ g) ∨ h))
          atp-strip $  -- Γ ⊢ (((((((((¬ a ∧ (a ∨ b)) ∧ (c ∨ d)) ∧ ((¬ b ∨ e) ∨ f)) ∧ (¬ c ∨ ¬ e)) ∧ (¬ c ∨ ¬ f)) ∧ ((¬ b ∨ g) ∨ h)) ∧ (¬ d ∨ ¬ g)) ∧ (¬ d ∨ ¬ h)) ⇒ ⊥)
            assume {Γ = Γ} $  -- Γ ⊢ ¬ (((((((((¬ a ∧ (a ∨ b)) ∧ (c ∨ d)) ∧ ((¬ b ∨ e) ∨ f)) ∧ (¬ c ∨ ¬ e)) ∧ (¬ c ∨ ¬ f)) ∧ ((¬ b ∨ g) ∨ h)) ∧ (¬ d ∨ ¬ g)) ∧ (¬ d ∨ ¬ h)) ⇒ ⊥)
              atp-neg subgoal₅

proof₆ : Γ ⊢ subgoal₆
proof₆ =
  RAA $
    atp-canonicalize $  -- Γ ⊢ ({ d h : Set} → ¬ d ∨ ¬ h)
      ∧-proj₁ $ -- 1: (((((((¬ a ∧ (¬ c ∨ ¬ e)) ∧ (¬ c ∨ ¬ f)) ∧ (¬ d ∨ ¬ g)) ∧ (¬ d ∨ ¬ h)) ∧ (a ∨ b)) ∧ (c ∨ d)) ∧ ((¬ b ∨ e) ∨ f))
        atp-canonicalize $  -- Γ ⊢ ((((((((¬ a ∧ (¬ c ∨ ¬ e)) ∧ (¬ c ∨ ¬ f)) ∧ (¬ d ∨ ¬ g)) ∧ (¬ d ∨ ¬ h)) ∧ (a ∨ b)) ∧ (c ∨ d)) ∧ ((¬ b ∨ e) ∨ f)) ∧ ((¬ b ∨ g) ∨ h))
          atp-strip $  -- Γ ⊢ (((((((((¬ a ∧ (a ∨ b)) ∧ (c ∨ d)) ∧ ((¬ b ∨ e) ∨ f)) ∧ (¬ c ∨ ¬ e)) ∧ (¬ c ∨ ¬ f)) ∧ ((¬ b ∨ g) ∨ h)) ∧ (¬ d ∨ ¬ g)) ∧ (¬ d ∨ ¬ h)) ⇒ ⊥)
            assume {Γ = Γ} $  -- Γ ⊢ ¬ (((((((((¬ a ∧ (a ∨ b)) ∧ (c ∨ d)) ∧ ((¬ b ∨ e) ∨ f)) ∧ (¬ c ∨ ¬ e)) ∧ (¬ c ∨ ¬ f)) ∧ ((¬ b ∨ g) ∨ h)) ∧ (¬ d ∨ ¬ g)) ∧ (¬ d ∨ ¬ h)) ⇒ ⊥)
              atp-neg subgoal₆

proof₇ : Γ ⊢ subgoal₇
proof₇ =
  RAA $
    atp-canonicalize $  -- Γ ⊢ ({ g h : Set} → g ∨ h)
      atp-simplify $  -- Γ ⊢ (g ∨ h)
        ∧-intro
          (
          ∧-proj₂ $ -- (((¬ b ∨ g) ∨ h) ≟ ((¬ b ∨ g) ∨ h))
            atp-canonicalize $  -- Γ ⊢ ((((((((¬ a ∧ (¬ c ∨ ¬ e)) ∧ (¬ c ∨ ¬ f)) ∧ (¬ d ∨ ¬ g)) ∧ (¬ d ∨ ¬ h)) ∧ (a ∨ b)) ∧ (c ∨ d)) ∧ ((¬ b ∨ e) ∨ f)) ∧ ((¬ b ∨ g) ∨ h))
              atp-strip $  -- Γ ⊢ (((((((((¬ a ∧ (a ∨ b)) ∧ (c ∨ d)) ∧ ((¬ b ∨ e) ∨ f)) ∧ (¬ c ∨ ¬ e)) ∧ (¬ c ∨ ¬ f)) ∧ ((¬ b ∨ g) ∨ h)) ∧ (¬ d ∨ ¬ g)) ∧ (¬ d ∨ ¬ h)) ⇒ ⊥)
                assume {Γ = Γ} $  -- Γ ⊢ ¬ (((((((((¬ a ∧ (a ∨ b)) ∧ (c ∨ d)) ∧ ((¬ b ∨ e) ∨ f)) ∧ (¬ c ∨ ¬ e)) ∧ (¬ c ∨ ¬ f)) ∧ ((¬ b ∨ g) ∨ h)) ∧ (¬ d ∨ ¬ g)) ∧ (¬ d ∨ ¬ h)) ⇒ ⊥)
                  atp-neg subgoal₇
          )
          (
          atp-simplify $  -- Γ ⊢ b
            ∧-intro
              (
              ∧-proj₁ $ -- 1: (((((((¬ a ∧ (¬ c ∨ ¬ e)) ∧ (¬ c ∨ ¬ f)) ∧ (¬ d ∨ ¬ g)) ∧ (¬ d ∨ ¬ h)) ∧ (a ∨ b)) ∧ (c ∨ d)) ∧ ((¬ b ∨ e) ∨ f))
                atp-canonicalize $  -- Γ ⊢ ((((((((¬ a ∧ (¬ c ∨ ¬ e)) ∧ (¬ c ∨ ¬ f)) ∧ (¬ d ∨ ¬ g)) ∧ (¬ d ∨ ¬ h)) ∧ (a ∨ b)) ∧ (c ∨ d)) ∧ ((¬ b ∨ e) ∨ f)) ∧ ((¬ b ∨ g) ∨ h))
                  atp-strip $  -- Γ ⊢ (((((((((¬ a ∧ (a ∨ b)) ∧ (c ∨ d)) ∧ ((¬ b ∨ e) ∨ f)) ∧ (¬ c ∨ ¬ e)) ∧ (¬ c ∨ ¬ f)) ∧ ((¬ b ∨ g) ∨ h)) ∧ (¬ d ∨ ¬ g)) ∧ (¬ d ∨ ¬ h)) ⇒ ⊥)
                    assume {Γ = Γ} $  -- Γ ⊢ ¬ (((((((((¬ a ∧ (a ∨ b)) ∧ (c ∨ d)) ∧ ((¬ b ∨ e) ∨ f)) ∧ (¬ c ∨ ¬ e)) ∧ (¬ c ∨ ¬ f)) ∧ ((¬ b ∨ g) ∨ h)) ∧ (¬ d ∨ ¬ g)) ∧ (¬ d ∨ ¬ h)) ⇒ ⊥)
                      atp-neg subgoal₇
              )
              (
              ∧-proj₁ $ -- 1: (((((((¬ a ∧ (¬ c ∨ ¬ e)) ∧ (¬ c ∨ ¬ f)) ∧ (¬ d ∨ ¬ g)) ∧ (¬ d ∨ ¬ h)) ∧ (a ∨ b)) ∧ (c ∨ d)) ∧ ((¬ b ∨ e) ∨ f))
                atp-canonicalize $  -- Γ ⊢ ((((((((¬ a ∧ (¬ c ∨ ¬ e)) ∧ (¬ c ∨ ¬ f)) ∧ (¬ d ∨ ¬ g)) ∧ (¬ d ∨ ¬ h)) ∧ (a ∨ b)) ∧ (c ∨ d)) ∧ ((¬ b ∨ e) ∨ f)) ∧ ((¬ b ∨ g) ∨ h))
                  atp-strip $  -- Γ ⊢ (((((((((¬ a ∧ (a ∨ b)) ∧ (c ∨ d)) ∧ ((¬ b ∨ e) ∨ f)) ∧ (¬ c ∨ ¬ e)) ∧ (¬ c ∨ ¬ f)) ∧ ((¬ b ∨ g) ∨ h)) ∧ (¬ d ∨ ¬ g)) ∧ (¬ d ∨ ¬ h)) ⇒ ⊥)
                    assume {Γ = Γ} $  -- Γ ⊢ ¬ (((((((((¬ a ∧ (a ∨ b)) ∧ (c ∨ d)) ∧ ((¬ b ∨ e) ∨ f)) ∧ (¬ c ∨ ¬ e)) ∧ (¬ c ∨ ¬ f)) ∧ ((¬ b ∨ g) ∨ h)) ∧ (¬ d ∨ ¬ g)) ∧ (¬ d ∨ ¬ h)) ⇒ ⊥)
                      atp-neg subgoal₇
              )
          )

proof₈ : Γ ⊢ subgoal₈
proof₈ =
  RAA $
    id -- resolve 4.
      (
              atp-canonicalize $  -- Γ ⊢ ({ g h : Set} → g ∨ h)
          atp-simplify $  -- Γ ⊢ (g ∨ h)
            ∧-intro
              (
              ∧-proj₂ $ -- (((¬ b ∨ g) ∨ h) ≟ ((¬ b ∨ g) ∨ h))
                atp-canonicalize $  -- Γ ⊢ ((((((((¬ a ∧ (¬ c ∨ ¬ e)) ∧ (¬ c ∨ ¬ f)) ∧ (¬ d ∨ ¬ g)) ∧ (¬ d ∨ ¬ h)) ∧ (a ∨ b)) ∧ (c ∨ d)) ∧ ((¬ b ∨ e) ∨ f)) ∧ ((¬ b ∨ g) ∨ h))
                  atp-strip $  -- Γ ⊢ (((((((((¬ a ∧ (a ∨ b)) ∧ (c ∨ d)) ∧ ((¬ b ∨ e) ∨ f)) ∧ (¬ c ∨ ¬ e)) ∧ (¬ c ∨ ¬ f)) ∧ ((¬ b ∨ g) ∨ h)) ∧ (¬ d ∨ ¬ g)) ∧ (¬ d ∨ ¬ h)) ⇒ ⊥)
                    assume {Γ = Γ} $  -- Γ ⊢ ¬ (((((((((¬ a ∧ (a ∨ b)) ∧ (c ∨ d)) ∧ ((¬ b ∨ e) ∨ f)) ∧ (¬ c ∨ ¬ e)) ∧ (¬ c ∨ ¬ f)) ∧ ((¬ b ∨ g) ∨ h)) ∧ (¬ d ∨ ¬ g)) ∧ (¬ d ∨ ¬ h)) ⇒ ⊥)
                      atp-neg subgoal₈
              )
              (
              atp-simplify $  -- Γ ⊢ b
                ∧-intro
                  (
                  ∧-proj₁ $ -- 1: (((((((¬ a ∧ (¬ c ∨ ¬ e)) ∧ (¬ c ∨ ¬ f)) ∧ (¬ d ∨ ¬ g)) ∧ (¬ d ∨ ¬ h)) ∧ (a ∨ b)) ∧ (c ∨ d)) ∧ ((¬ b ∨ e) ∨ f))
                    atp-canonicalize $  -- Γ ⊢ ((((((((¬ a ∧ (¬ c ∨ ¬ e)) ∧ (¬ c ∨ ¬ f)) ∧ (¬ d ∨ ¬ g)) ∧ (¬ d ∨ ¬ h)) ∧ (a ∨ b)) ∧ (c ∨ d)) ∧ ((¬ b ∨ e) ∨ f)) ∧ ((¬ b ∨ g) ∨ h))
                      atp-strip $  -- Γ ⊢ (((((((((¬ a ∧ (a ∨ b)) ∧ (c ∨ d)) ∧ ((¬ b ∨ e) ∨ f)) ∧ (¬ c ∨ ¬ e)) ∧ (¬ c ∨ ¬ f)) ∧ ((¬ b ∨ g) ∨ h)) ∧ (¬ d ∨ ¬ g)) ∧ (¬ d ∨ ¬ h)) ⇒ ⊥)
                        assume {Γ = Γ} $  -- Γ ⊢ ¬ (((((((((¬ a ∧ (a ∨ b)) ∧ (c ∨ d)) ∧ ((¬ b ∨ e) ∨ f)) ∧ (¬ c ∨ ¬ e)) ∧ (¬ c ∨ ¬ f)) ∧ ((¬ b ∨ g) ∨ h)) ∧ (¬ d ∨ ¬ g)) ∧ (¬ d ∨ ¬ h)) ⇒ ⊥)
                          atp-neg subgoal₈
                  )
                  (
                  ∧-proj₁ $ -- 1: (((((((¬ a ∧ (¬ c ∨ ¬ e)) ∧ (¬ c ∨ ¬ f)) ∧ (¬ d ∨ ¬ g)) ∧ (¬ d ∨ ¬ h)) ∧ (a ∨ b)) ∧ (c ∨ d)) ∧ ((¬ b ∨ e) ∨ f))
                    atp-canonicalize $  -- Γ ⊢ ((((((((¬ a ∧ (¬ c ∨ ¬ e)) ∧ (¬ c ∨ ¬ f)) ∧ (¬ d ∨ ¬ g)) ∧ (¬ d ∨ ¬ h)) ∧ (a ∨ b)) ∧ (c ∨ d)) ∧ ((¬ b ∨ e) ∨ f)) ∧ ((¬ b ∨ g) ∨ h))
                      atp-strip $  -- Γ ⊢ (((((((((¬ a ∧ (a ∨ b)) ∧ (c ∨ d)) ∧ ((¬ b ∨ e) ∨ f)) ∧ (¬ c ∨ ¬ e)) ∧ (¬ c ∨ ¬ f)) ∧ ((¬ b ∨ g) ∨ h)) ∧ (¬ d ∨ ¬ g)) ∧ (¬ d ∨ ¬ h)) ⇒ ⊥)
                        assume {Γ = Γ} $  -- Γ ⊢ ¬ (((((((((¬ a ∧ (a ∨ b)) ∧ (c ∨ d)) ∧ ((¬ b ∨ e) ∨ f)) ∧ (¬ c ∨ ¬ e)) ∧ (¬ c ∨ ¬ f)) ∧ ((¬ b ∨ g) ∨ h)) ∧ (¬ d ∨ ¬ g)) ∧ (¬ d ∨ ¬ h)) ⇒ ⊥)
                          atp-neg subgoal₈
                  )
              )
      )
      (
              atp-canonicalize $  -- Γ ⊢ ({ d h : Set} → ¬ d ∨ ¬ h)
          ∧-proj₁ $ -- 1: (((((((¬ a ∧ (¬ c ∨ ¬ e)) ∧ (¬ c ∨ ¬ f)) ∧ (¬ d ∨ ¬ g)) ∧ (¬ d ∨ ¬ h)) ∧ (a ∨ b)) ∧ (c ∨ d)) ∧ ((¬ b ∨ e) ∨ f))
            atp-canonicalize $  -- Γ ⊢ ((((((((¬ a ∧ (¬ c ∨ ¬ e)) ∧ (¬ c ∨ ¬ f)) ∧ (¬ d ∨ ¬ g)) ∧ (¬ d ∨ ¬ h)) ∧ (a ∨ b)) ∧ (c ∨ d)) ∧ ((¬ b ∨ e) ∨ f)) ∧ ((¬ b ∨ g) ∨ h))
              atp-strip $  -- Γ ⊢ (((((((((¬ a ∧ (a ∨ b)) ∧ (c ∨ d)) ∧ ((¬ b ∨ e) ∨ f)) ∧ (¬ c ∨ ¬ e)) ∧ (¬ c ∨ ¬ f)) ∧ ((¬ b ∨ g) ∨ h)) ∧ (¬ d ∨ ¬ g)) ∧ (¬ d ∨ ¬ h)) ⇒ ⊥)
                assume {Γ = Γ} $  -- Γ ⊢ ¬ (((((((((¬ a ∧ (a ∨ b)) ∧ (c ∨ d)) ∧ ((¬ b ∨ e) ∨ f)) ∧ (¬ c ∨ ¬ e)) ∧ (¬ c ∨ ¬ f)) ∧ ((¬ b ∨ g) ∨ h)) ∧ (¬ d ∨ ¬ g)) ∧ (¬ d ∨ ¬ h)) ⇒ ⊥)
                  atp-neg subgoal₈
      )

proof₉ : Γ ⊢ subgoal₉
proof₉ =
  RAA $
    id -- resolve 4.
      (
              atp-canonicalize $  -- Γ ⊢ ({ c d : Set} → c ∨ d)
          ∧-proj₁ $ -- 1: (((((((¬ a ∧ (¬ c ∨ ¬ e)) ∧ (¬ c ∨ ¬ f)) ∧ (¬ d ∨ ¬ g)) ∧ (¬ d ∨ ¬ h)) ∧ (a ∨ b)) ∧ (c ∨ d)) ∧ ((¬ b ∨ e) ∨ f))
            atp-canonicalize $  -- Γ ⊢ ((((((((¬ a ∧ (¬ c ∨ ¬ e)) ∧ (¬ c ∨ ¬ f)) ∧ (¬ d ∨ ¬ g)) ∧ (¬ d ∨ ¬ h)) ∧ (a ∨ b)) ∧ (c ∨ d)) ∧ ((¬ b ∨ e) ∨ f)) ∧ ((¬ b ∨ g) ∨ h))
              atp-strip $  -- Γ ⊢ (((((((((¬ a ∧ (a ∨ b)) ∧ (c ∨ d)) ∧ ((¬ b ∨ e) ∨ f)) ∧ (¬ c ∨ ¬ e)) ∧ (¬ c ∨ ¬ f)) ∧ ((¬ b ∨ g) ∨ h)) ∧ (¬ d ∨ ¬ g)) ∧ (¬ d ∨ ¬ h)) ⇒ ⊥)
                assume {Γ = Γ} $  -- Γ ⊢ ¬ (((((((((¬ a ∧ (a ∨ b)) ∧ (c ∨ d)) ∧ ((¬ b ∨ e) ∨ f)) ∧ (¬ c ∨ ¬ e)) ∧ (¬ c ∨ ¬ f)) ∧ ((¬ b ∨ g) ∨ h)) ∧ (¬ d ∨ ¬ g)) ∧ (¬ d ∨ ¬ h)) ⇒ ⊥)
                  atp-neg subgoal₉
      )
      (
              id -- resolve 4.
          (
                      atp-canonicalize $  -- Γ ⊢ ({ g h : Set} → g ∨ h)
              atp-simplify $  -- Γ ⊢ (g ∨ h)
                ∧-intro
                  (
                  ∧-proj₂ $ -- (((¬ b ∨ g) ∨ h) ≟ ((¬ b ∨ g) ∨ h))
                    atp-canonicalize $  -- Γ ⊢ ((((((((¬ a ∧ (¬ c ∨ ¬ e)) ∧ (¬ c ∨ ¬ f)) ∧ (¬ d ∨ ¬ g)) ∧ (¬ d ∨ ¬ h)) ∧ (a ∨ b)) ∧ (c ∨ d)) ∧ ((¬ b ∨ e) ∨ f)) ∧ ((¬ b ∨ g) ∨ h))
                      atp-strip $  -- Γ ⊢ (((((((((¬ a ∧ (a ∨ b)) ∧ (c ∨ d)) ∧ ((¬ b ∨ e) ∨ f)) ∧ (¬ c ∨ ¬ e)) ∧ (¬ c ∨ ¬ f)) ∧ ((¬ b ∨ g) ∨ h)) ∧ (¬ d ∨ ¬ g)) ∧ (¬ d ∨ ¬ h)) ⇒ ⊥)
                        assume {Γ = Γ} $  -- Γ ⊢ ¬ (((((((((¬ a ∧ (a ∨ b)) ∧ (c ∨ d)) ∧ ((¬ b ∨ e) ∨ f)) ∧ (¬ c ∨ ¬ e)) ∧ (¬ c ∨ ¬ f)) ∧ ((¬ b ∨ g) ∨ h)) ∧ (¬ d ∨ ¬ g)) ∧ (¬ d ∨ ¬ h)) ⇒ ⊥)
                          atp-neg subgoal₉
                  )
                  (
                  atp-simplify $  -- Γ ⊢ b
                    ∧-intro
                      (
                      ∧-proj₁ $ -- 1: (((((((¬ a ∧ (¬ c ∨ ¬ e)) ∧ (¬ c ∨ ¬ f)) ∧ (¬ d ∨ ¬ g)) ∧ (¬ d ∨ ¬ h)) ∧ (a ∨ b)) ∧ (c ∨ d)) ∧ ((¬ b ∨ e) ∨ f))
                        atp-canonicalize $  -- Γ ⊢ ((((((((¬ a ∧ (¬ c ∨ ¬ e)) ∧ (¬ c ∨ ¬ f)) ∧ (¬ d ∨ ¬ g)) ∧ (¬ d ∨ ¬ h)) ∧ (a ∨ b)) ∧ (c ∨ d)) ∧ ((¬ b ∨ e) ∨ f)) ∧ ((¬ b ∨ g) ∨ h))
                          atp-strip $  -- Γ ⊢ (((((((((¬ a ∧ (a ∨ b)) ∧ (c ∨ d)) ∧ ((¬ b ∨ e) ∨ f)) ∧ (¬ c ∨ ¬ e)) ∧ (¬ c ∨ ¬ f)) ∧ ((¬ b ∨ g) ∨ h)) ∧ (¬ d ∨ ¬ g)) ∧ (¬ d ∨ ¬ h)) ⇒ ⊥)
                            assume {Γ = Γ} $  -- Γ ⊢ ¬ (((((((((¬ a ∧ (a ∨ b)) ∧ (c ∨ d)) ∧ ((¬ b ∨ e) ∨ f)) ∧ (¬ c ∨ ¬ e)) ∧ (¬ c ∨ ¬ f)) ∧ ((¬ b ∨ g) ∨ h)) ∧ (¬ d ∨ ¬ g)) ∧ (¬ d ∨ ¬ h)) ⇒ ⊥)
                              atp-neg subgoal₉
                      )
                      (
                      ∧-proj₁ $ -- 1: (((((((¬ a ∧ (¬ c ∨ ¬ e)) ∧ (¬ c ∨ ¬ f)) ∧ (¬ d ∨ ¬ g)) ∧ (¬ d ∨ ¬ h)) ∧ (a ∨ b)) ∧ (c ∨ d)) ∧ ((¬ b ∨ e) ∨ f))
                        atp-canonicalize $  -- Γ ⊢ ((((((((¬ a ∧ (¬ c ∨ ¬ e)) ∧ (¬ c ∨ ¬ f)) ∧ (¬ d ∨ ¬ g)) ∧ (¬ d ∨ ¬ h)) ∧ (a ∨ b)) ∧ (c ∨ d)) ∧ ((¬ b ∨ e) ∨ f)) ∧ ((¬ b ∨ g) ∨ h))
                          atp-strip $  -- Γ ⊢ (((((((((¬ a ∧ (a ∨ b)) ∧ (c ∨ d)) ∧ ((¬ b ∨ e) ∨ f)) ∧ (¬ c ∨ ¬ e)) ∧ (¬ c ∨ ¬ f)) ∧ ((¬ b ∨ g) ∨ h)) ∧ (¬ d ∨ ¬ g)) ∧ (¬ d ∨ ¬ h)) ⇒ ⊥)
                            assume {Γ = Γ} $  -- Γ ⊢ ¬ (((((((((¬ a ∧ (a ∨ b)) ∧ (c ∨ d)) ∧ ((¬ b ∨ e) ∨ f)) ∧ (¬ c ∨ ¬ e)) ∧ (¬ c ∨ ¬ f)) ∧ ((¬ b ∨ g) ∨ h)) ∧ (¬ d ∨ ¬ g)) ∧ (¬ d ∨ ¬ h)) ⇒ ⊥)
                              atp-neg subgoal₉
                      )
                  )
          )
          (
                      atp-canonicalize $  -- Γ ⊢ ({ d h : Set} → ¬ d ∨ ¬ h)
              ∧-proj₁ $ -- 1: (((((((¬ a ∧ (¬ c ∨ ¬ e)) ∧ (¬ c ∨ ¬ f)) ∧ (¬ d ∨ ¬ g)) ∧ (¬ d ∨ ¬ h)) ∧ (a ∨ b)) ∧ (c ∨ d)) ∧ ((¬ b ∨ e) ∨ f))
                atp-canonicalize $  -- Γ ⊢ ((((((((¬ a ∧ (¬ c ∨ ¬ e)) ∧ (¬ c ∨ ¬ f)) ∧ (¬ d ∨ ¬ g)) ∧ (¬ d ∨ ¬ h)) ∧ (a ∨ b)) ∧ (c ∨ d)) ∧ ((¬ b ∨ e) ∨ f)) ∧ ((¬ b ∨ g) ∨ h))
                  atp-strip $  -- Γ ⊢ (((((((((¬ a ∧ (a ∨ b)) ∧ (c ∨ d)) ∧ ((¬ b ∨ e) ∨ f)) ∧ (¬ c ∨ ¬ e)) ∧ (¬ c ∨ ¬ f)) ∧ ((¬ b ∨ g) ∨ h)) ∧ (¬ d ∨ ¬ g)) ∧ (¬ d ∨ ¬ h)) ⇒ ⊥)
                    assume {Γ = Γ} $  -- Γ ⊢ ¬ (((((((((¬ a ∧ (a ∨ b)) ∧ (c ∨ d)) ∧ ((¬ b ∨ e) ∨ f)) ∧ (¬ c ∨ ¬ e)) ∧ (¬ c ∨ ¬ f)) ∧ ((¬ b ∨ g) ∨ h)) ∧ (¬ d ∨ ¬ g)) ∧ (¬ d ∨ ¬ h)) ⇒ ⊥)
                      atp-neg subgoal₉
          )
      )

proof₁₀ : Γ ⊢ subgoal₁₀
proof₁₀ =
  RAA $
    id -- resolve 4.
      (
              id -- resolve 4.
          (
                      atp-canonicalize $  -- Γ ⊢ ({ c d : Set} → c ∨ d)
              ∧-proj₁ $ -- 1: (((((((¬ a ∧ (¬ c ∨ ¬ e)) ∧ (¬ c ∨ ¬ f)) ∧ (¬ d ∨ ¬ g)) ∧ (¬ d ∨ ¬ h)) ∧ (a ∨ b)) ∧ (c ∨ d)) ∧ ((¬ b ∨ e) ∨ f))
                atp-canonicalize $  -- Γ ⊢ ((((((((¬ a ∧ (¬ c ∨ ¬ e)) ∧ (¬ c ∨ ¬ f)) ∧ (¬ d ∨ ¬ g)) ∧ (¬ d ∨ ¬ h)) ∧ (a ∨ b)) ∧ (c ∨ d)) ∧ ((¬ b ∨ e) ∨ f)) ∧ ((¬ b ∨ g) ∨ h))
                  atp-strip $  -- Γ ⊢ (((((((((¬ a ∧ (a ∨ b)) ∧ (c ∨ d)) ∧ ((¬ b ∨ e) ∨ f)) ∧ (¬ c ∨ ¬ e)) ∧ (¬ c ∨ ¬ f)) ∧ ((¬ b ∨ g) ∨ h)) ∧ (¬ d ∨ ¬ g)) ∧ (¬ d ∨ ¬ h)) ⇒ ⊥)
                    assume {Γ = Γ} $  -- Γ ⊢ ¬ (((((((((¬ a ∧ (a ∨ b)) ∧ (c ∨ d)) ∧ ((¬ b ∨ e) ∨ f)) ∧ (¬ c ∨ ¬ e)) ∧ (¬ c ∨ ¬ f)) ∧ ((¬ b ∨ g) ∨ h)) ∧ (¬ d ∨ ¬ g)) ∧ (¬ d ∨ ¬ h)) ⇒ ⊥)
                      atp-neg subgoal₁₀
          )
          (
                      id -- resolve 4.
              (
                              atp-canonicalize $  -- Γ ⊢ ({ g h : Set} → g ∨ h)
                  atp-simplify $  -- Γ ⊢ (g ∨ h)
                    ∧-intro
                      (
                      ∧-proj₂ $ -- (((¬ b ∨ g) ∨ h) ≟ ((¬ b ∨ g) ∨ h))
                        atp-canonicalize $  -- Γ ⊢ ((((((((¬ a ∧ (¬ c ∨ ¬ e)) ∧ (¬ c ∨ ¬ f)) ∧ (¬ d ∨ ¬ g)) ∧ (¬ d ∨ ¬ h)) ∧ (a ∨ b)) ∧ (c ∨ d)) ∧ ((¬ b ∨ e) ∨ f)) ∧ ((¬ b ∨ g) ∨ h))
                          atp-strip $  -- Γ ⊢ (((((((((¬ a ∧ (a ∨ b)) ∧ (c ∨ d)) ∧ ((¬ b ∨ e) ∨ f)) ∧ (¬ c ∨ ¬ e)) ∧ (¬ c ∨ ¬ f)) ∧ ((¬ b ∨ g) ∨ h)) ∧ (¬ d ∨ ¬ g)) ∧ (¬ d ∨ ¬ h)) ⇒ ⊥)
                            assume {Γ = Γ} $  -- Γ ⊢ ¬ (((((((((¬ a ∧ (a ∨ b)) ∧ (c ∨ d)) ∧ ((¬ b ∨ e) ∨ f)) ∧ (¬ c ∨ ¬ e)) ∧ (¬ c ∨ ¬ f)) ∧ ((¬ b ∨ g) ∨ h)) ∧ (¬ d ∨ ¬ g)) ∧ (¬ d ∨ ¬ h)) ⇒ ⊥)
                              atp-neg subgoal₁₀
                      )
                      (
                      atp-simplify $  -- Γ ⊢ b
                        ∧-intro
                          (
                          ∧-proj₁ $ -- 1: (((((((¬ a ∧ (¬ c ∨ ¬ e)) ∧ (¬ c ∨ ¬ f)) ∧ (¬ d ∨ ¬ g)) ∧ (¬ d ∨ ¬ h)) ∧ (a ∨ b)) ∧ (c ∨ d)) ∧ ((¬ b ∨ e) ∨ f))
                            atp-canonicalize $  -- Γ ⊢ ((((((((¬ a ∧ (¬ c ∨ ¬ e)) ∧ (¬ c ∨ ¬ f)) ∧ (¬ d ∨ ¬ g)) ∧ (¬ d ∨ ¬ h)) ∧ (a ∨ b)) ∧ (c ∨ d)) ∧ ((¬ b ∨ e) ∨ f)) ∧ ((¬ b ∨ g) ∨ h))
                              atp-strip $  -- Γ ⊢ (((((((((¬ a ∧ (a ∨ b)) ∧ (c ∨ d)) ∧ ((¬ b ∨ e) ∨ f)) ∧ (¬ c ∨ ¬ e)) ∧ (¬ c ∨ ¬ f)) ∧ ((¬ b ∨ g) ∨ h)) ∧ (¬ d ∨ ¬ g)) ∧ (¬ d ∨ ¬ h)) ⇒ ⊥)
                                assume {Γ = Γ} $  -- Γ ⊢ ¬ (((((((((¬ a ∧ (a ∨ b)) ∧ (c ∨ d)) ∧ ((¬ b ∨ e) ∨ f)) ∧ (¬ c ∨ ¬ e)) ∧ (¬ c ∨ ¬ f)) ∧ ((¬ b ∨ g) ∨ h)) ∧ (¬ d ∨ ¬ g)) ∧ (¬ d ∨ ¬ h)) ⇒ ⊥)
                                  atp-neg subgoal₁₀
                          )
                          (
                          ∧-proj₁ $ -- 1: (((((((¬ a ∧ (¬ c ∨ ¬ e)) ∧ (¬ c ∨ ¬ f)) ∧ (¬ d ∨ ¬ g)) ∧ (¬ d ∨ ¬ h)) ∧ (a ∨ b)) ∧ (c ∨ d)) ∧ ((¬ b ∨ e) ∨ f))
                            atp-canonicalize $  -- Γ ⊢ ((((((((¬ a ∧ (¬ c ∨ ¬ e)) ∧ (¬ c ∨ ¬ f)) ∧ (¬ d ∨ ¬ g)) ∧ (¬ d ∨ ¬ h)) ∧ (a ∨ b)) ∧ (c ∨ d)) ∧ ((¬ b ∨ e) ∨ f)) ∧ ((¬ b ∨ g) ∨ h))
                              atp-strip $  -- Γ ⊢ (((((((((¬ a ∧ (a ∨ b)) ∧ (c ∨ d)) ∧ ((¬ b ∨ e) ∨ f)) ∧ (¬ c ∨ ¬ e)) ∧ (¬ c ∨ ¬ f)) ∧ ((¬ b ∨ g) ∨ h)) ∧ (¬ d ∨ ¬ g)) ∧ (¬ d ∨ ¬ h)) ⇒ ⊥)
                                assume {Γ = Γ} $  -- Γ ⊢ ¬ (((((((((¬ a ∧ (a ∨ b)) ∧ (c ∨ d)) ∧ ((¬ b ∨ e) ∨ f)) ∧ (¬ c ∨ ¬ e)) ∧ (¬ c ∨ ¬ f)) ∧ ((¬ b ∨ g) ∨ h)) ∧ (¬ d ∨ ¬ g)) ∧ (¬ d ∨ ¬ h)) ⇒ ⊥)
                                  atp-neg subgoal₁₀
                          )
                      )
              )
              (
                              atp-canonicalize $  -- Γ ⊢ ({ d h : Set} → ¬ d ∨ ¬ h)
                  ∧-proj₁ $ -- 1: (((((((¬ a ∧ (¬ c ∨ ¬ e)) ∧ (¬ c ∨ ¬ f)) ∧ (¬ d ∨ ¬ g)) ∧ (¬ d ∨ ¬ h)) ∧ (a ∨ b)) ∧ (c ∨ d)) ∧ ((¬ b ∨ e) ∨ f))
                    atp-canonicalize $  -- Γ ⊢ ((((((((¬ a ∧ (¬ c ∨ ¬ e)) ∧ (¬ c ∨ ¬ f)) ∧ (¬ d ∨ ¬ g)) ∧ (¬ d ∨ ¬ h)) ∧ (a ∨ b)) ∧ (c ∨ d)) ∧ ((¬ b ∨ e) ∨ f)) ∧ ((¬ b ∨ g) ∨ h))
                      atp-strip $  -- Γ ⊢ (((((((((¬ a ∧ (a ∨ b)) ∧ (c ∨ d)) ∧ ((¬ b ∨ e) ∨ f)) ∧ (¬ c ∨ ¬ e)) ∧ (¬ c ∨ ¬ f)) ∧ ((¬ b ∨ g) ∨ h)) ∧ (¬ d ∨ ¬ g)) ∧ (¬ d ∨ ¬ h)) ⇒ ⊥)
                        assume {Γ = Γ} $  -- Γ ⊢ ¬ (((((((((¬ a ∧ (a ∨ b)) ∧ (c ∨ d)) ∧ ((¬ b ∨ e) ∨ f)) ∧ (¬ c ∨ ¬ e)) ∧ (¬ c ∨ ¬ f)) ∧ ((¬ b ∨ g) ∨ h)) ∧ (¬ d ∨ ¬ g)) ∧ (¬ d ∨ ¬ h)) ⇒ ⊥)
                          atp-neg subgoal₁₀
              )
          )
      )
      (
              atp-canonicalize $  -- Γ ⊢ ({ d g : Set} → ¬ d ∨ ¬ g)
          ∧-proj₁ $ -- 1: (((((((¬ a ∧ (¬ c ∨ ¬ e)) ∧ (¬ c ∨ ¬ f)) ∧ (¬ d ∨ ¬ g)) ∧ (¬ d ∨ ¬ h)) ∧ (a ∨ b)) ∧ (c ∨ d)) ∧ ((¬ b ∨ e) ∨ f))
            atp-canonicalize $  -- Γ ⊢ ((((((((¬ a ∧ (¬ c ∨ ¬ e)) ∧ (¬ c ∨ ¬ f)) ∧ (¬ d ∨ ¬ g)) ∧ (¬ d ∨ ¬ h)) ∧ (a ∨ b)) ∧ (c ∨ d)) ∧ ((¬ b ∨ e) ∨ f)) ∧ ((¬ b ∨ g) ∨ h))
              atp-strip $  -- Γ ⊢ (((((((((¬ a ∧ (a ∨ b)) ∧ (c ∨ d)) ∧ ((¬ b ∨ e) ∨ f)) ∧ (¬ c ∨ ¬ e)) ∧ (¬ c ∨ ¬ f)) ∧ ((¬ b ∨ g) ∨ h)) ∧ (¬ d ∨ ¬ g)) ∧ (¬ d ∨ ¬ h)) ⇒ ⊥)
                assume {Γ = Γ} $  -- Γ ⊢ ¬ (((((((((¬ a ∧ (a ∨ b)) ∧ (c ∨ d)) ∧ ((¬ b ∨ e) ∨ f)) ∧ (¬ c ∨ ¬ e)) ∧ (¬ c ∨ ¬ f)) ∧ ((¬ b ∨ g) ∨ h)) ∧ (¬ d ∨ ¬ g)) ∧ (¬ d ∨ ¬ h)) ⇒ ⊥)
                  atp-neg subgoal₁₀
      )

proof₁₁ : Γ ⊢ subgoal₁₁
proof₁₁ =
  RAA $
    id -- resolve 4.
      (
              atp-canonicalize $  -- Γ ⊢ ({ c d : Set} → c ∨ d)
          ∧-proj₁ $ -- 1: (((((((¬ a ∧ (¬ c ∨ ¬ e)) ∧ (¬ c ∨ ¬ f)) ∧ (¬ d ∨ ¬ g)) ∧ (¬ d ∨ ¬ h)) ∧ (a ∨ b)) ∧ (c ∨ d)) ∧ ((¬ b ∨ e) ∨ f))
            atp-canonicalize $  -- Γ ⊢ ((((((((¬ a ∧ (¬ c ∨ ¬ e)) ∧ (¬ c ∨ ¬ f)) ∧ (¬ d ∨ ¬ g)) ∧ (¬ d ∨ ¬ h)) ∧ (a ∨ b)) ∧ (c ∨ d)) ∧ ((¬ b ∨ e) ∨ f)) ∧ ((¬ b ∨ g) ∨ h))
              atp-strip $  -- Γ ⊢ (((((((((¬ a ∧ (a ∨ b)) ∧ (c ∨ d)) ∧ ((¬ b ∨ e) ∨ f)) ∧ (¬ c ∨ ¬ e)) ∧ (¬ c ∨ ¬ f)) ∧ ((¬ b ∨ g) ∨ h)) ∧ (¬ d ∨ ¬ g)) ∧ (¬ d ∨ ¬ h)) ⇒ ⊥)
                assume {Γ = Γ} $  -- Γ ⊢ ¬ (((((((((¬ a ∧ (a ∨ b)) ∧ (c ∨ d)) ∧ ((¬ b ∨ e) ∨ f)) ∧ (¬ c ∨ ¬ e)) ∧ (¬ c ∨ ¬ f)) ∧ ((¬ b ∨ g) ∨ h)) ∧ (¬ d ∨ ¬ g)) ∧ (¬ d ∨ ¬ h)) ⇒ ⊥)
                  atp-neg subgoal₁₁
      )
      (
              id -- resolve 4.
          (
                      id -- resolve 4.
              (
                              atp-canonicalize $  -- Γ ⊢ ({ c d : Set} → c ∨ d)
                  ∧-proj₁ $ -- 1: (((((((¬ a ∧ (¬ c ∨ ¬ e)) ∧ (¬ c ∨ ¬ f)) ∧ (¬ d ∨ ¬ g)) ∧ (¬ d ∨ ¬ h)) ∧ (a ∨ b)) ∧ (c ∨ d)) ∧ ((¬ b ∨ e) ∨ f))
                    atp-canonicalize $  -- Γ ⊢ ((((((((¬ a ∧ (¬ c ∨ ¬ e)) ∧ (¬ c ∨ ¬ f)) ∧ (¬ d ∨ ¬ g)) ∧ (¬ d ∨ ¬ h)) ∧ (a ∨ b)) ∧ (c ∨ d)) ∧ ((¬ b ∨ e) ∨ f)) ∧ ((¬ b ∨ g) ∨ h))
                      atp-strip $  -- Γ ⊢ (((((((((¬ a ∧ (a ∨ b)) ∧ (c ∨ d)) ∧ ((¬ b ∨ e) ∨ f)) ∧ (¬ c ∨ ¬ e)) ∧ (¬ c ∨ ¬ f)) ∧ ((¬ b ∨ g) ∨ h)) ∧ (¬ d ∨ ¬ g)) ∧ (¬ d ∨ ¬ h)) ⇒ ⊥)
                        assume {Γ = Γ} $  -- Γ ⊢ ¬ (((((((((¬ a ∧ (a ∨ b)) ∧ (c ∨ d)) ∧ ((¬ b ∨ e) ∨ f)) ∧ (¬ c ∨ ¬ e)) ∧ (¬ c ∨ ¬ f)) ∧ ((¬ b ∨ g) ∨ h)) ∧ (¬ d ∨ ¬ g)) ∧ (¬ d ∨ ¬ h)) ⇒ ⊥)
                          atp-neg subgoal₁₁
              )
              (
                              id -- resolve 4.
                  (
                                      atp-canonicalize $  -- Γ ⊢ ({ g h : Set} → g ∨ h)
                      atp-simplify $  -- Γ ⊢ (g ∨ h)
                        ∧-intro
                          (
                          ∧-proj₂ $ -- (((¬ b ∨ g) ∨ h) ≟ ((¬ b ∨ g) ∨ h))
                            atp-canonicalize $  -- Γ ⊢ ((((((((¬ a ∧ (¬ c ∨ ¬ e)) ∧ (¬ c ∨ ¬ f)) ∧ (¬ d ∨ ¬ g)) ∧ (¬ d ∨ ¬ h)) ∧ (a ∨ b)) ∧ (c ∨ d)) ∧ ((¬ b ∨ e) ∨ f)) ∧ ((¬ b ∨ g) ∨ h))
                              atp-strip $  -- Γ ⊢ (((((((((¬ a ∧ (a ∨ b)) ∧ (c ∨ d)) ∧ ((¬ b ∨ e) ∨ f)) ∧ (¬ c ∨ ¬ e)) ∧ (¬ c ∨ ¬ f)) ∧ ((¬ b ∨ g) ∨ h)) ∧ (¬ d ∨ ¬ g)) ∧ (¬ d ∨ ¬ h)) ⇒ ⊥)
                                assume {Γ = Γ} $  -- Γ ⊢ ¬ (((((((((¬ a ∧ (a ∨ b)) ∧ (c ∨ d)) ∧ ((¬ b ∨ e) ∨ f)) ∧ (¬ c ∨ ¬ e)) ∧ (¬ c ∨ ¬ f)) ∧ ((¬ b ∨ g) ∨ h)) ∧ (¬ d ∨ ¬ g)) ∧ (¬ d ∨ ¬ h)) ⇒ ⊥)
                                  atp-neg subgoal₁₁
                          )
                          (
                          atp-simplify $  -- Γ ⊢ b
                            ∧-intro
                              (
                              ∧-proj₁ $ -- 1: (((((((¬ a ∧ (¬ c ∨ ¬ e)) ∧ (¬ c ∨ ¬ f)) ∧ (¬ d ∨ ¬ g)) ∧ (¬ d ∨ ¬ h)) ∧ (a ∨ b)) ∧ (c ∨ d)) ∧ ((¬ b ∨ e) ∨ f))
                                atp-canonicalize $  -- Γ ⊢ ((((((((¬ a ∧ (¬ c ∨ ¬ e)) ∧ (¬ c ∨ ¬ f)) ∧ (¬ d ∨ ¬ g)) ∧ (¬ d ∨ ¬ h)) ∧ (a ∨ b)) ∧ (c ∨ d)) ∧ ((¬ b ∨ e) ∨ f)) ∧ ((¬ b ∨ g) ∨ h))
                                  atp-strip $  -- Γ ⊢ (((((((((¬ a ∧ (a ∨ b)) ∧ (c ∨ d)) ∧ ((¬ b ∨ e) ∨ f)) ∧ (¬ c ∨ ¬ e)) ∧ (¬ c ∨ ¬ f)) ∧ ((¬ b ∨ g) ∨ h)) ∧ (¬ d ∨ ¬ g)) ∧ (¬ d ∨ ¬ h)) ⇒ ⊥)
                                    assume {Γ = Γ} $  -- Γ ⊢ ¬ (((((((((¬ a ∧ (a ∨ b)) ∧ (c ∨ d)) ∧ ((¬ b ∨ e) ∨ f)) ∧ (¬ c ∨ ¬ e)) ∧ (¬ c ∨ ¬ f)) ∧ ((¬ b ∨ g) ∨ h)) ∧ (¬ d ∨ ¬ g)) ∧ (¬ d ∨ ¬ h)) ⇒ ⊥)
                                      atp-neg subgoal₁₁
                              )
                              (
                              ∧-proj₁ $ -- 1: (((((((¬ a ∧ (¬ c ∨ ¬ e)) ∧ (¬ c ∨ ¬ f)) ∧ (¬ d ∨ ¬ g)) ∧ (¬ d ∨ ¬ h)) ∧ (a ∨ b)) ∧ (c ∨ d)) ∧ ((¬ b ∨ e) ∨ f))
                                atp-canonicalize $  -- Γ ⊢ ((((((((¬ a ∧ (¬ c ∨ ¬ e)) ∧ (¬ c ∨ ¬ f)) ∧ (¬ d ∨ ¬ g)) ∧ (¬ d ∨ ¬ h)) ∧ (a ∨ b)) ∧ (c ∨ d)) ∧ ((¬ b ∨ e) ∨ f)) ∧ ((¬ b ∨ g) ∨ h))
                                  atp-strip $  -- Γ ⊢ (((((((((¬ a ∧ (a ∨ b)) ∧ (c ∨ d)) ∧ ((¬ b ∨ e) ∨ f)) ∧ (¬ c ∨ ¬ e)) ∧ (¬ c ∨ ¬ f)) ∧ ((¬ b ∨ g) ∨ h)) ∧ (¬ d ∨ ¬ g)) ∧ (¬ d ∨ ¬ h)) ⇒ ⊥)
                                    assume {Γ = Γ} $  -- Γ ⊢ ¬ (((((((((¬ a ∧ (a ∨ b)) ∧ (c ∨ d)) ∧ ((¬ b ∨ e) ∨ f)) ∧ (¬ c ∨ ¬ e)) ∧ (¬ c ∨ ¬ f)) ∧ ((¬ b ∨ g) ∨ h)) ∧ (¬ d ∨ ¬ g)) ∧ (¬ d ∨ ¬ h)) ⇒ ⊥)
                                      atp-neg subgoal₁₁
                              )
                          )
                  )
                  (
                                      atp-canonicalize $  -- Γ ⊢ ({ d h : Set} → ¬ d ∨ ¬ h)
                      ∧-proj₁ $ -- 1: (((((((¬ a ∧ (¬ c ∨ ¬ e)) ∧ (¬ c ∨ ¬ f)) ∧ (¬ d ∨ ¬ g)) ∧ (¬ d ∨ ¬ h)) ∧ (a ∨ b)) ∧ (c ∨ d)) ∧ ((¬ b ∨ e) ∨ f))
                        atp-canonicalize $  -- Γ ⊢ ((((((((¬ a ∧ (¬ c ∨ ¬ e)) ∧ (¬ c ∨ ¬ f)) ∧ (¬ d ∨ ¬ g)) ∧ (¬ d ∨ ¬ h)) ∧ (a ∨ b)) ∧ (c ∨ d)) ∧ ((¬ b ∨ e) ∨ f)) ∧ ((¬ b ∨ g) ∨ h))
                          atp-strip $  -- Γ ⊢ (((((((((¬ a ∧ (a ∨ b)) ∧ (c ∨ d)) ∧ ((¬ b ∨ e) ∨ f)) ∧ (¬ c ∨ ¬ e)) ∧ (¬ c ∨ ¬ f)) ∧ ((¬ b ∨ g) ∨ h)) ∧ (¬ d ∨ ¬ g)) ∧ (¬ d ∨ ¬ h)) ⇒ ⊥)
                            assume {Γ = Γ} $  -- Γ ⊢ ¬ (((((((((¬ a ∧ (a ∨ b)) ∧ (c ∨ d)) ∧ ((¬ b ∨ e) ∨ f)) ∧ (¬ c ∨ ¬ e)) ∧ (¬ c ∨ ¬ f)) ∧ ((¬ b ∨ g) ∨ h)) ∧ (¬ d ∨ ¬ g)) ∧ (¬ d ∨ ¬ h)) ⇒ ⊥)
                              atp-neg subgoal₁₁
                  )
              )
          )
          (
                      atp-canonicalize $  -- Γ ⊢ ({ d g : Set} → ¬ d ∨ ¬ g)
              ∧-proj₁ $ -- 1: (((((((¬ a ∧ (¬ c ∨ ¬ e)) ∧ (¬ c ∨ ¬ f)) ∧ (¬ d ∨ ¬ g)) ∧ (¬ d ∨ ¬ h)) ∧ (a ∨ b)) ∧ (c ∨ d)) ∧ ((¬ b ∨ e) ∨ f))
                atp-canonicalize $  -- Γ ⊢ ((((((((¬ a ∧ (¬ c ∨ ¬ e)) ∧ (¬ c ∨ ¬ f)) ∧ (¬ d ∨ ¬ g)) ∧ (¬ d ∨ ¬ h)) ∧ (a ∨ b)) ∧ (c ∨ d)) ∧ ((¬ b ∨ e) ∨ f)) ∧ ((¬ b ∨ g) ∨ h))
                  atp-strip $  -- Γ ⊢ (((((((((¬ a ∧ (a ∨ b)) ∧ (c ∨ d)) ∧ ((¬ b ∨ e) ∨ f)) ∧ (¬ c ∨ ¬ e)) ∧ (¬ c ∨ ¬ f)) ∧ ((¬ b ∨ g) ∨ h)) ∧ (¬ d ∨ ¬ g)) ∧ (¬ d ∨ ¬ h)) ⇒ ⊥)
                    assume {Γ = Γ} $  -- Γ ⊢ ¬ (((((((((¬ a ∧ (a ∨ b)) ∧ (c ∨ d)) ∧ ((¬ b ∨ e) ∨ f)) ∧ (¬ c ∨ ¬ e)) ∧ (¬ c ∨ ¬ f)) ∧ ((¬ b ∨ g) ∨ h)) ∧ (¬ d ∨ ¬ g)) ∧ (¬ d ∨ ¬ h)) ⇒ ⊥)
                      atp-neg subgoal₁₁
          )
      )

proof₁₂ : Γ ⊢ subgoal₁₂
proof₁₂ =
  RAA $
    id -- resolve 4.
      (
              id -- resolve 4.
          (
                      atp-canonicalize $  -- Γ ⊢ ({ c d : Set} → c ∨ d)
              ∧-proj₁ $ -- 1: (((((((¬ a ∧ (¬ c ∨ ¬ e)) ∧ (¬ c ∨ ¬ f)) ∧ (¬ d ∨ ¬ g)) ∧ (¬ d ∨ ¬ h)) ∧ (a ∨ b)) ∧ (c ∨ d)) ∧ ((¬ b ∨ e) ∨ f))
                atp-canonicalize $  -- Γ ⊢ ((((((((¬ a ∧ (¬ c ∨ ¬ e)) ∧ (¬ c ∨ ¬ f)) ∧ (¬ d ∨ ¬ g)) ∧ (¬ d ∨ ¬ h)) ∧ (a ∨ b)) ∧ (c ∨ d)) ∧ ((¬ b ∨ e) ∨ f)) ∧ ((¬ b ∨ g) ∨ h))
                  atp-strip $  -- Γ ⊢ (((((((((¬ a ∧ (a ∨ b)) ∧ (c ∨ d)) ∧ ((¬ b ∨ e) ∨ f)) ∧ (¬ c ∨ ¬ e)) ∧ (¬ c ∨ ¬ f)) ∧ ((¬ b ∨ g) ∨ h)) ∧ (¬ d ∨ ¬ g)) ∧ (¬ d ∨ ¬ h)) ⇒ ⊥)
                    assume {Γ = Γ} $  -- Γ ⊢ ¬ (((((((((¬ a ∧ (a ∨ b)) ∧ (c ∨ d)) ∧ ((¬ b ∨ e) ∨ f)) ∧ (¬ c ∨ ¬ e)) ∧ (¬ c ∨ ¬ f)) ∧ ((¬ b ∨ g) ∨ h)) ∧ (¬ d ∨ ¬ g)) ∧ (¬ d ∨ ¬ h)) ⇒ ⊥)
                      atp-neg subgoal₁₂
          )
          (
                      id -- resolve 4.
              (
                              id -- resolve 4.
                  (
                                      atp-canonicalize $  -- Γ ⊢ ({ c d : Set} → c ∨ d)
                      ∧-proj₁ $ -- 1: (((((((¬ a ∧ (¬ c ∨ ¬ e)) ∧ (¬ c ∨ ¬ f)) ∧ (¬ d ∨ ¬ g)) ∧ (¬ d ∨ ¬ h)) ∧ (a ∨ b)) ∧ (c ∨ d)) ∧ ((¬ b ∨ e) ∨ f))
                        atp-canonicalize $  -- Γ ⊢ ((((((((¬ a ∧ (¬ c ∨ ¬ e)) ∧ (¬ c ∨ ¬ f)) ∧ (¬ d ∨ ¬ g)) ∧ (¬ d ∨ ¬ h)) ∧ (a ∨ b)) ∧ (c ∨ d)) ∧ ((¬ b ∨ e) ∨ f)) ∧ ((¬ b ∨ g) ∨ h))
                          atp-strip $  -- Γ ⊢ (((((((((¬ a ∧ (a ∨ b)) ∧ (c ∨ d)) ∧ ((¬ b ∨ e) ∨ f)) ∧ (¬ c ∨ ¬ e)) ∧ (¬ c ∨ ¬ f)) ∧ ((¬ b ∨ g) ∨ h)) ∧ (¬ d ∨ ¬ g)) ∧ (¬ d ∨ ¬ h)) ⇒ ⊥)
                            assume {Γ = Γ} $  -- Γ ⊢ ¬ (((((((((¬ a ∧ (a ∨ b)) ∧ (c ∨ d)) ∧ ((¬ b ∨ e) ∨ f)) ∧ (¬ c ∨ ¬ e)) ∧ (¬ c ∨ ¬ f)) ∧ ((¬ b ∨ g) ∨ h)) ∧ (¬ d ∨ ¬ g)) ∧ (¬ d ∨ ¬ h)) ⇒ ⊥)
                              atp-neg subgoal₁₂
                  )
                  (
                                      id -- resolve 4.
                      (
                                              atp-canonicalize $  -- Γ ⊢ ({ g h : Set} → g ∨ h)
                          atp-simplify $  -- Γ ⊢ (g ∨ h)
                            ∧-intro
                              (
                              ∧-proj₂ $ -- (((¬ b ∨ g) ∨ h) ≟ ((¬ b ∨ g) ∨ h))
                                atp-canonicalize $  -- Γ ⊢ ((((((((¬ a ∧ (¬ c ∨ ¬ e)) ∧ (¬ c ∨ ¬ f)) ∧ (¬ d ∨ ¬ g)) ∧ (¬ d ∨ ¬ h)) ∧ (a ∨ b)) ∧ (c ∨ d)) ∧ ((¬ b ∨ e) ∨ f)) ∧ ((¬ b ∨ g) ∨ h))
                                  atp-strip $  -- Γ ⊢ (((((((((¬ a ∧ (a ∨ b)) ∧ (c ∨ d)) ∧ ((¬ b ∨ e) ∨ f)) ∧ (¬ c ∨ ¬ e)) ∧ (¬ c ∨ ¬ f)) ∧ ((¬ b ∨ g) ∨ h)) ∧ (¬ d ∨ ¬ g)) ∧ (¬ d ∨ ¬ h)) ⇒ ⊥)
                                    assume {Γ = Γ} $  -- Γ ⊢ ¬ (((((((((¬ a ∧ (a ∨ b)) ∧ (c ∨ d)) ∧ ((¬ b ∨ e) ∨ f)) ∧ (¬ c ∨ ¬ e)) ∧ (¬ c ∨ ¬ f)) ∧ ((¬ b ∨ g) ∨ h)) ∧ (¬ d ∨ ¬ g)) ∧ (¬ d ∨ ¬ h)) ⇒ ⊥)
                                      atp-neg subgoal₁₂
                              )
                              (
                              atp-simplify $  -- Γ ⊢ b
                                ∧-intro
                                  (
                                  ∧-proj₁ $ -- 1: (((((((¬ a ∧ (¬ c ∨ ¬ e)) ∧ (¬ c ∨ ¬ f)) ∧ (¬ d ∨ ¬ g)) ∧ (¬ d ∨ ¬ h)) ∧ (a ∨ b)) ∧ (c ∨ d)) ∧ ((¬ b ∨ e) ∨ f))
                                    atp-canonicalize $  -- Γ ⊢ ((((((((¬ a ∧ (¬ c ∨ ¬ e)) ∧ (¬ c ∨ ¬ f)) ∧ (¬ d ∨ ¬ g)) ∧ (¬ d ∨ ¬ h)) ∧ (a ∨ b)) ∧ (c ∨ d)) ∧ ((¬ b ∨ e) ∨ f)) ∧ ((¬ b ∨ g) ∨ h))
                                      atp-strip $  -- Γ ⊢ (((((((((¬ a ∧ (a ∨ b)) ∧ (c ∨ d)) ∧ ((¬ b ∨ e) ∨ f)) ∧ (¬ c ∨ ¬ e)) ∧ (¬ c ∨ ¬ f)) ∧ ((¬ b ∨ g) ∨ h)) ∧ (¬ d ∨ ¬ g)) ∧ (¬ d ∨ ¬ h)) ⇒ ⊥)
                                        assume {Γ = Γ} $  -- Γ ⊢ ¬ (((((((((¬ a ∧ (a ∨ b)) ∧ (c ∨ d)) ∧ ((¬ b ∨ e) ∨ f)) ∧ (¬ c ∨ ¬ e)) ∧ (¬ c ∨ ¬ f)) ∧ ((¬ b ∨ g) ∨ h)) ∧ (¬ d ∨ ¬ g)) ∧ (¬ d ∨ ¬ h)) ⇒ ⊥)
                                          atp-neg subgoal₁₂
                                  )
                                  (
                                  ∧-proj₁ $ -- 1: (((((((¬ a ∧ (¬ c ∨ ¬ e)) ∧ (¬ c ∨ ¬ f)) ∧ (¬ d ∨ ¬ g)) ∧ (¬ d ∨ ¬ h)) ∧ (a ∨ b)) ∧ (c ∨ d)) ∧ ((¬ b ∨ e) ∨ f))
                                    atp-canonicalize $  -- Γ ⊢ ((((((((¬ a ∧ (¬ c ∨ ¬ e)) ∧ (¬ c ∨ ¬ f)) ∧ (¬ d ∨ ¬ g)) ∧ (¬ d ∨ ¬ h)) ∧ (a ∨ b)) ∧ (c ∨ d)) ∧ ((¬ b ∨ e) ∨ f)) ∧ ((¬ b ∨ g) ∨ h))
                                      atp-strip $  -- Γ ⊢ (((((((((¬ a ∧ (a ∨ b)) ∧ (c ∨ d)) ∧ ((¬ b ∨ e) ∨ f)) ∧ (¬ c ∨ ¬ e)) ∧ (¬ c ∨ ¬ f)) ∧ ((¬ b ∨ g) ∨ h)) ∧ (¬ d ∨ ¬ g)) ∧ (¬ d ∨ ¬ h)) ⇒ ⊥)
                                        assume {Γ = Γ} $  -- Γ ⊢ ¬ (((((((((¬ a ∧ (a ∨ b)) ∧ (c ∨ d)) ∧ ((¬ b ∨ e) ∨ f)) ∧ (¬ c ∨ ¬ e)) ∧ (¬ c ∨ ¬ f)) ∧ ((¬ b ∨ g) ∨ h)) ∧ (¬ d ∨ ¬ g)) ∧ (¬ d ∨ ¬ h)) ⇒ ⊥)
                                          atp-neg subgoal₁₂
                                  )
                              )
                      )
                      (
                                              atp-canonicalize $  -- Γ ⊢ ({ d h : Set} → ¬ d ∨ ¬ h)
                          ∧-proj₁ $ -- 1: (((((((¬ a ∧ (¬ c ∨ ¬ e)) ∧ (¬ c ∨ ¬ f)) ∧ (¬ d ∨ ¬ g)) ∧ (¬ d ∨ ¬ h)) ∧ (a ∨ b)) ∧ (c ∨ d)) ∧ ((¬ b ∨ e) ∨ f))
                            atp-canonicalize $  -- Γ ⊢ ((((((((¬ a ∧ (¬ c ∨ ¬ e)) ∧ (¬ c ∨ ¬ f)) ∧ (¬ d ∨ ¬ g)) ∧ (¬ d ∨ ¬ h)) ∧ (a ∨ b)) ∧ (c ∨ d)) ∧ ((¬ b ∨ e) ∨ f)) ∧ ((¬ b ∨ g) ∨ h))
                              atp-strip $  -- Γ ⊢ (((((((((¬ a ∧ (a ∨ b)) ∧ (c ∨ d)) ∧ ((¬ b ∨ e) ∨ f)) ∧ (¬ c ∨ ¬ e)) ∧ (¬ c ∨ ¬ f)) ∧ ((¬ b ∨ g) ∨ h)) ∧ (¬ d ∨ ¬ g)) ∧ (¬ d ∨ ¬ h)) ⇒ ⊥)
                                assume {Γ = Γ} $  -- Γ ⊢ ¬ (((((((((¬ a ∧ (a ∨ b)) ∧ (c ∨ d)) ∧ ((¬ b ∨ e) ∨ f)) ∧ (¬ c ∨ ¬ e)) ∧ (¬ c ∨ ¬ f)) ∧ ((¬ b ∨ g) ∨ h)) ∧ (¬ d ∨ ¬ g)) ∧ (¬ d ∨ ¬ h)) ⇒ ⊥)
                                  atp-neg subgoal₁₂
                      )
                  )
              )
              (
                              atp-canonicalize $  -- Γ ⊢ ({ d g : Set} → ¬ d ∨ ¬ g)
                  ∧-proj₁ $ -- 1: (((((((¬ a ∧ (¬ c ∨ ¬ e)) ∧ (¬ c ∨ ¬ f)) ∧ (¬ d ∨ ¬ g)) ∧ (¬ d ∨ ¬ h)) ∧ (a ∨ b)) ∧ (c ∨ d)) ∧ ((¬ b ∨ e) ∨ f))
                    atp-canonicalize $  -- Γ ⊢ ((((((((¬ a ∧ (¬ c ∨ ¬ e)) ∧ (¬ c ∨ ¬ f)) ∧ (¬ d ∨ ¬ g)) ∧ (¬ d ∨ ¬ h)) ∧ (a ∨ b)) ∧ (c ∨ d)) ∧ ((¬ b ∨ e) ∨ f)) ∧ ((¬ b ∨ g) ∨ h))
                      atp-strip $  -- Γ ⊢ (((((((((¬ a ∧ (a ∨ b)) ∧ (c ∨ d)) ∧ ((¬ b ∨ e) ∨ f)) ∧ (¬ c ∨ ¬ e)) ∧ (¬ c ∨ ¬ f)) ∧ ((¬ b ∨ g) ∨ h)) ∧ (¬ d ∨ ¬ g)) ∧ (¬ d ∨ ¬ h)) ⇒ ⊥)
                        assume {Γ = Γ} $  -- Γ ⊢ ¬ (((((((((¬ a ∧ (a ∨ b)) ∧ (c ∨ d)) ∧ ((¬ b ∨ e) ∨ f)) ∧ (¬ c ∨ ¬ e)) ∧ (¬ c ∨ ¬ f)) ∧ ((¬ b ∨ g) ∨ h)) ∧ (¬ d ∨ ¬ g)) ∧ (¬ d ∨ ¬ h)) ⇒ ⊥)
                          atp-neg subgoal₁₂
              )
          )
      )
      (
              id -- resolve 4.
          (
                      atp-canonicalize $  -- Γ ⊢ ({ e f : Set} → e ∨ f)
              atp-simplify $  -- Γ ⊢ (e ∨ f)
                ∧-intro
                  (
                  ∧-proj₁ $ -- 1: (((((((¬ a ∧ (¬ c ∨ ¬ e)) ∧ (¬ c ∨ ¬ f)) ∧ (¬ d ∨ ¬ g)) ∧ (¬ d ∨ ¬ h)) ∧ (a ∨ b)) ∧ (c ∨ d)) ∧ ((¬ b ∨ e) ∨ f))
                    atp-canonicalize $  -- Γ ⊢ ((((((((¬ a ∧ (¬ c ∨ ¬ e)) ∧ (¬ c ∨ ¬ f)) ∧ (¬ d ∨ ¬ g)) ∧ (¬ d ∨ ¬ h)) ∧ (a ∨ b)) ∧ (c ∨ d)) ∧ ((¬ b ∨ e) ∨ f)) ∧ ((¬ b ∨ g) ∨ h))
                      atp-strip $  -- Γ ⊢ (((((((((¬ a ∧ (a ∨ b)) ∧ (c ∨ d)) ∧ ((¬ b ∨ e) ∨ f)) ∧ (¬ c ∨ ¬ e)) ∧ (¬ c ∨ ¬ f)) ∧ ((¬ b ∨ g) ∨ h)) ∧ (¬ d ∨ ¬ g)) ∧ (¬ d ∨ ¬ h)) ⇒ ⊥)
                        assume {Γ = Γ} $  -- Γ ⊢ ¬ (((((((((¬ a ∧ (a ∨ b)) ∧ (c ∨ d)) ∧ ((¬ b ∨ e) ∨ f)) ∧ (¬ c ∨ ¬ e)) ∧ (¬ c ∨ ¬ f)) ∧ ((¬ b ∨ g) ∨ h)) ∧ (¬ d ∨ ¬ g)) ∧ (¬ d ∨ ¬ h)) ⇒ ⊥)
                          atp-neg subgoal₁₂
                  )
                  (
                  atp-simplify $  -- Γ ⊢ b
                    ∧-intro
                      (
                      ∧-proj₁ $ -- 1: (((((((¬ a ∧ (¬ c ∨ ¬ e)) ∧ (¬ c ∨ ¬ f)) ∧ (¬ d ∨ ¬ g)) ∧ (¬ d ∨ ¬ h)) ∧ (a ∨ b)) ∧ (c ∨ d)) ∧ ((¬ b ∨ e) ∨ f))
                        atp-canonicalize $  -- Γ ⊢ ((((((((¬ a ∧ (¬ c ∨ ¬ e)) ∧ (¬ c ∨ ¬ f)) ∧ (¬ d ∨ ¬ g)) ∧ (¬ d ∨ ¬ h)) ∧ (a ∨ b)) ∧ (c ∨ d)) ∧ ((¬ b ∨ e) ∨ f)) ∧ ((¬ b ∨ g) ∨ h))
                          atp-strip $  -- Γ ⊢ (((((((((¬ a ∧ (a ∨ b)) ∧ (c ∨ d)) ∧ ((¬ b ∨ e) ∨ f)) ∧ (¬ c ∨ ¬ e)) ∧ (¬ c ∨ ¬ f)) ∧ ((¬ b ∨ g) ∨ h)) ∧ (¬ d ∨ ¬ g)) ∧ (¬ d ∨ ¬ h)) ⇒ ⊥)
                            assume {Γ = Γ} $  -- Γ ⊢ ¬ (((((((((¬ a ∧ (a ∨ b)) ∧ (c ∨ d)) ∧ ((¬ b ∨ e) ∨ f)) ∧ (¬ c ∨ ¬ e)) ∧ (¬ c ∨ ¬ f)) ∧ ((¬ b ∨ g) ∨ h)) ∧ (¬ d ∨ ¬ g)) ∧ (¬ d ∨ ¬ h)) ⇒ ⊥)
                              atp-neg subgoal₁₂
                      )
                      (
                      ∧-proj₁ $ -- 1: (((((((¬ a ∧ (¬ c ∨ ¬ e)) ∧ (¬ c ∨ ¬ f)) ∧ (¬ d ∨ ¬ g)) ∧ (¬ d ∨ ¬ h)) ∧ (a ∨ b)) ∧ (c ∨ d)) ∧ ((¬ b ∨ e) ∨ f))
                        atp-canonicalize $  -- Γ ⊢ ((((((((¬ a ∧ (¬ c ∨ ¬ e)) ∧ (¬ c ∨ ¬ f)) ∧ (¬ d ∨ ¬ g)) ∧ (¬ d ∨ ¬ h)) ∧ (a ∨ b)) ∧ (c ∨ d)) ∧ ((¬ b ∨ e) ∨ f)) ∧ ((¬ b ∨ g) ∨ h))
                          atp-strip $  -- Γ ⊢ (((((((((¬ a ∧ (a ∨ b)) ∧ (c ∨ d)) ∧ ((¬ b ∨ e) ∨ f)) ∧ (¬ c ∨ ¬ e)) ∧ (¬ c ∨ ¬ f)) ∧ ((¬ b ∨ g) ∨ h)) ∧ (¬ d ∨ ¬ g)) ∧ (¬ d ∨ ¬ h)) ⇒ ⊥)
                            assume {Γ = Γ} $  -- Γ ⊢ ¬ (((((((((¬ a ∧ (a ∨ b)) ∧ (c ∨ d)) ∧ ((¬ b ∨ e) ∨ f)) ∧ (¬ c ∨ ¬ e)) ∧ (¬ c ∨ ¬ f)) ∧ ((¬ b ∨ g) ∨ h)) ∧ (¬ d ∨ ¬ g)) ∧ (¬ d ∨ ¬ h)) ⇒ ⊥)
                              atp-neg subgoal₁₂
                      )
                  )
          )
          (
                      atp-canonicalize $  -- Γ ⊢ ({ c f : Set} → ¬ c ∨ ¬ f)
              ∧-proj₁ $ -- 1: (((((((¬ a ∧ (¬ c ∨ ¬ e)) ∧ (¬ c ∨ ¬ f)) ∧ (¬ d ∨ ¬ g)) ∧ (¬ d ∨ ¬ h)) ∧ (a ∨ b)) ∧ (c ∨ d)) ∧ ((¬ b ∨ e) ∨ f))
                atp-canonicalize $  -- Γ ⊢ ((((((((¬ a ∧ (¬ c ∨ ¬ e)) ∧ (¬ c ∨ ¬ f)) ∧ (¬ d ∨ ¬ g)) ∧ (¬ d ∨ ¬ h)) ∧ (a ∨ b)) ∧ (c ∨ d)) ∧ ((¬ b ∨ e) ∨ f)) ∧ ((¬ b ∨ g) ∨ h))
                  atp-strip $  -- Γ ⊢ (((((((((¬ a ∧ (a ∨ b)) ∧ (c ∨ d)) ∧ ((¬ b ∨ e) ∨ f)) ∧ (¬ c ∨ ¬ e)) ∧ (¬ c ∨ ¬ f)) ∧ ((¬ b ∨ g) ∨ h)) ∧ (¬ d ∨ ¬ g)) ∧ (¬ d ∨ ¬ h)) ⇒ ⊥)
                    assume {Γ = Γ} $  -- Γ ⊢ ¬ (((((((((¬ a ∧ (a ∨ b)) ∧ (c ∨ d)) ∧ ((¬ b ∨ e) ∨ f)) ∧ (¬ c ∨ ¬ e)) ∧ (¬ c ∨ ¬ f)) ∧ ((¬ b ∨ g) ∨ h)) ∧ (¬ d ∨ ¬ g)) ∧ (¬ d ∨ ¬ h)) ⇒ ⊥)
                      atp-neg subgoal₁₂
          )
      )

proof₁₃ : Γ ⊢ subgoal₁₃
proof₁₃ =
  RAA $
    id -- resolve 4.
      (
              id -- resolve 4.
          (
                      id -- resolve 4.
              (
                              atp-canonicalize $  -- Γ ⊢ ({ c d : Set} → c ∨ d)
                  ∧-proj₁ $ -- 1: (((((((¬ a ∧ (¬ c ∨ ¬ e)) ∧ (¬ c ∨ ¬ f)) ∧ (¬ d ∨ ¬ g)) ∧ (¬ d ∨ ¬ h)) ∧ (a ∨ b)) ∧ (c ∨ d)) ∧ ((¬ b ∨ e) ∨ f))
                    atp-canonicalize $  -- Γ ⊢ ((((((((¬ a ∧ (¬ c ∨ ¬ e)) ∧ (¬ c ∨ ¬ f)) ∧ (¬ d ∨ ¬ g)) ∧ (¬ d ∨ ¬ h)) ∧ (a ∨ b)) ∧ (c ∨ d)) ∧ ((¬ b ∨ e) ∨ f)) ∧ ((¬ b ∨ g) ∨ h))
                      atp-strip $  -- Γ ⊢ (((((((((¬ a ∧ (a ∨ b)) ∧ (c ∨ d)) ∧ ((¬ b ∨ e) ∨ f)) ∧ (¬ c ∨ ¬ e)) ∧ (¬ c ∨ ¬ f)) ∧ ((¬ b ∨ g) ∨ h)) ∧ (¬ d ∨ ¬ g)) ∧ (¬ d ∨ ¬ h)) ⇒ ⊥)
                        assume {Γ = Γ} $  -- Γ ⊢ ¬ (((((((((¬ a ∧ (a ∨ b)) ∧ (c ∨ d)) ∧ ((¬ b ∨ e) ∨ f)) ∧ (¬ c ∨ ¬ e)) ∧ (¬ c ∨ ¬ f)) ∧ ((¬ b ∨ g) ∨ h)) ∧ (¬ d ∨ ¬ g)) ∧ (¬ d ∨ ¬ h)) ⇒ ⊥)
                          atp-neg subgoal₁₃
              )
              (
                              id -- resolve 4.
                  (
                                      id -- resolve 4.
                      (
                                              atp-canonicalize $  -- Γ ⊢ ({ c d : Set} → c ∨ d)
                          ∧-proj₁ $ -- 1: (((((((¬ a ∧ (¬ c ∨ ¬ e)) ∧ (¬ c ∨ ¬ f)) ∧ (¬ d ∨ ¬ g)) ∧ (¬ d ∨ ¬ h)) ∧ (a ∨ b)) ∧ (c ∨ d)) ∧ ((¬ b ∨ e) ∨ f))
                            atp-canonicalize $  -- Γ ⊢ ((((((((¬ a ∧ (¬ c ∨ ¬ e)) ∧ (¬ c ∨ ¬ f)) ∧ (¬ d ∨ ¬ g)) ∧ (¬ d ∨ ¬ h)) ∧ (a ∨ b)) ∧ (c ∨ d)) ∧ ((¬ b ∨ e) ∨ f)) ∧ ((¬ b ∨ g) ∨ h))
                              atp-strip $  -- Γ ⊢ (((((((((¬ a ∧ (a ∨ b)) ∧ (c ∨ d)) ∧ ((¬ b ∨ e) ∨ f)) ∧ (¬ c ∨ ¬ e)) ∧ (¬ c ∨ ¬ f)) ∧ ((¬ b ∨ g) ∨ h)) ∧ (¬ d ∨ ¬ g)) ∧ (¬ d ∨ ¬ h)) ⇒ ⊥)
                                assume {Γ = Γ} $  -- Γ ⊢ ¬ (((((((((¬ a ∧ (a ∨ b)) ∧ (c ∨ d)) ∧ ((¬ b ∨ e) ∨ f)) ∧ (¬ c ∨ ¬ e)) ∧ (¬ c ∨ ¬ f)) ∧ ((¬ b ∨ g) ∨ h)) ∧ (¬ d ∨ ¬ g)) ∧ (¬ d ∨ ¬ h)) ⇒ ⊥)
                                  atp-neg subgoal₁₃
                      )
                      (
                                              id -- resolve 4.
                          (
                                                      atp-canonicalize $  -- Γ ⊢ ({ g h : Set} → g ∨ h)
                              atp-simplify $  -- Γ ⊢ (g ∨ h)
                                ∧-intro
                                  (
                                  ∧-proj₂ $ -- (((¬ b ∨ g) ∨ h) ≟ ((¬ b ∨ g) ∨ h))
                                    atp-canonicalize $  -- Γ ⊢ ((((((((¬ a ∧ (¬ c ∨ ¬ e)) ∧ (¬ c ∨ ¬ f)) ∧ (¬ d ∨ ¬ g)) ∧ (¬ d ∨ ¬ h)) ∧ (a ∨ b)) ∧ (c ∨ d)) ∧ ((¬ b ∨ e) ∨ f)) ∧ ((¬ b ∨ g) ∨ h))
                                      atp-strip $  -- Γ ⊢ (((((((((¬ a ∧ (a ∨ b)) ∧ (c ∨ d)) ∧ ((¬ b ∨ e) ∨ f)) ∧ (¬ c ∨ ¬ e)) ∧ (¬ c ∨ ¬ f)) ∧ ((¬ b ∨ g) ∨ h)) ∧ (¬ d ∨ ¬ g)) ∧ (¬ d ∨ ¬ h)) ⇒ ⊥)
                                        assume {Γ = Γ} $  -- Γ ⊢ ¬ (((((((((¬ a ∧ (a ∨ b)) ∧ (c ∨ d)) ∧ ((¬ b ∨ e) ∨ f)) ∧ (¬ c ∨ ¬ e)) ∧ (¬ c ∨ ¬ f)) ∧ ((¬ b ∨ g) ∨ h)) ∧ (¬ d ∨ ¬ g)) ∧ (¬ d ∨ ¬ h)) ⇒ ⊥)
                                          atp-neg subgoal₁₃
                                  )
                                  (
                                  atp-simplify $  -- Γ ⊢ b
                                    ∧-intro
                                      (
                                      ∧-proj₁ $ -- 1: (((((((¬ a ∧ (¬ c ∨ ¬ e)) ∧ (¬ c ∨ ¬ f)) ∧ (¬ d ∨ ¬ g)) ∧ (¬ d ∨ ¬ h)) ∧ (a ∨ b)) ∧ (c ∨ d)) ∧ ((¬ b ∨ e) ∨ f))
                                        atp-canonicalize $  -- Γ ⊢ ((((((((¬ a ∧ (¬ c ∨ ¬ e)) ∧ (¬ c ∨ ¬ f)) ∧ (¬ d ∨ ¬ g)) ∧ (¬ d ∨ ¬ h)) ∧ (a ∨ b)) ∧ (c ∨ d)) ∧ ((¬ b ∨ e) ∨ f)) ∧ ((¬ b ∨ g) ∨ h))
                                          atp-strip $  -- Γ ⊢ (((((((((¬ a ∧ (a ∨ b)) ∧ (c ∨ d)) ∧ ((¬ b ∨ e) ∨ f)) ∧ (¬ c ∨ ¬ e)) ∧ (¬ c ∨ ¬ f)) ∧ ((¬ b ∨ g) ∨ h)) ∧ (¬ d ∨ ¬ g)) ∧ (¬ d ∨ ¬ h)) ⇒ ⊥)
                                            assume {Γ = Γ} $  -- Γ ⊢ ¬ (((((((((¬ a ∧ (a ∨ b)) ∧ (c ∨ d)) ∧ ((¬ b ∨ e) ∨ f)) ∧ (¬ c ∨ ¬ e)) ∧ (¬ c ∨ ¬ f)) ∧ ((¬ b ∨ g) ∨ h)) ∧ (¬ d ∨ ¬ g)) ∧ (¬ d ∨ ¬ h)) ⇒ ⊥)
                                              atp-neg subgoal₁₃
                                      )
                                      (
                                      ∧-proj₁ $ -- 1: (((((((¬ a ∧ (¬ c ∨ ¬ e)) ∧ (¬ c ∨ ¬ f)) ∧ (¬ d ∨ ¬ g)) ∧ (¬ d ∨ ¬ h)) ∧ (a ∨ b)) ∧ (c ∨ d)) ∧ ((¬ b ∨ e) ∨ f))
                                        atp-canonicalize $  -- Γ ⊢ ((((((((¬ a ∧ (¬ c ∨ ¬ e)) ∧ (¬ c ∨ ¬ f)) ∧ (¬ d ∨ ¬ g)) ∧ (¬ d ∨ ¬ h)) ∧ (a ∨ b)) ∧ (c ∨ d)) ∧ ((¬ b ∨ e) ∨ f)) ∧ ((¬ b ∨ g) ∨ h))
                                          atp-strip $  -- Γ ⊢ (((((((((¬ a ∧ (a ∨ b)) ∧ (c ∨ d)) ∧ ((¬ b ∨ e) ∨ f)) ∧ (¬ c ∨ ¬ e)) ∧ (¬ c ∨ ¬ f)) ∧ ((¬ b ∨ g) ∨ h)) ∧ (¬ d ∨ ¬ g)) ∧ (¬ d ∨ ¬ h)) ⇒ ⊥)
                                            assume {Γ = Γ} $  -- Γ ⊢ ¬ (((((((((¬ a ∧ (a ∨ b)) ∧ (c ∨ d)) ∧ ((¬ b ∨ e) ∨ f)) ∧ (¬ c ∨ ¬ e)) ∧ (¬ c ∨ ¬ f)) ∧ ((¬ b ∨ g) ∨ h)) ∧ (¬ d ∨ ¬ g)) ∧ (¬ d ∨ ¬ h)) ⇒ ⊥)
                                              atp-neg subgoal₁₃
                                      )
                                  )
                          )
                          (
                                                      atp-canonicalize $  -- Γ ⊢ ({ d h : Set} → ¬ d ∨ ¬ h)
                              ∧-proj₁ $ -- 1: (((((((¬ a ∧ (¬ c ∨ ¬ e)) ∧ (¬ c ∨ ¬ f)) ∧ (¬ d ∨ ¬ g)) ∧ (¬ d ∨ ¬ h)) ∧ (a ∨ b)) ∧ (c ∨ d)) ∧ ((¬ b ∨ e) ∨ f))
                                atp-canonicalize $  -- Γ ⊢ ((((((((¬ a ∧ (¬ c ∨ ¬ e)) ∧ (¬ c ∨ ¬ f)) ∧ (¬ d ∨ ¬ g)) ∧ (¬ d ∨ ¬ h)) ∧ (a ∨ b)) ∧ (c ∨ d)) ∧ ((¬ b ∨ e) ∨ f)) ∧ ((¬ b ∨ g) ∨ h))
                                  atp-strip $  -- Γ ⊢ (((((((((¬ a ∧ (a ∨ b)) ∧ (c ∨ d)) ∧ ((¬ b ∨ e) ∨ f)) ∧ (¬ c ∨ ¬ e)) ∧ (¬ c ∨ ¬ f)) ∧ ((¬ b ∨ g) ∨ h)) ∧ (¬ d ∨ ¬ g)) ∧ (¬ d ∨ ¬ h)) ⇒ ⊥)
                                    assume {Γ = Γ} $  -- Γ ⊢ ¬ (((((((((¬ a ∧ (a ∨ b)) ∧ (c ∨ d)) ∧ ((¬ b ∨ e) ∨ f)) ∧ (¬ c ∨ ¬ e)) ∧ (¬ c ∨ ¬ f)) ∧ ((¬ b ∨ g) ∨ h)) ∧ (¬ d ∨ ¬ g)) ∧ (¬ d ∨ ¬ h)) ⇒ ⊥)
                                      atp-neg subgoal₁₃
                          )
                      )
                  )
                  (
                                      atp-canonicalize $  -- Γ ⊢ ({ d g : Set} → ¬ d ∨ ¬ g)
                      ∧-proj₁ $ -- 1: (((((((¬ a ∧ (¬ c ∨ ¬ e)) ∧ (¬ c ∨ ¬ f)) ∧ (¬ d ∨ ¬ g)) ∧ (¬ d ∨ ¬ h)) ∧ (a ∨ b)) ∧ (c ∨ d)) ∧ ((¬ b ∨ e) ∨ f))
                        atp-canonicalize $  -- Γ ⊢ ((((((((¬ a ∧ (¬ c ∨ ¬ e)) ∧ (¬ c ∨ ¬ f)) ∧ (¬ d ∨ ¬ g)) ∧ (¬ d ∨ ¬ h)) ∧ (a ∨ b)) ∧ (c ∨ d)) ∧ ((¬ b ∨ e) ∨ f)) ∧ ((¬ b ∨ g) ∨ h))
                          atp-strip $  -- Γ ⊢ (((((((((¬ a ∧ (a ∨ b)) ∧ (c ∨ d)) ∧ ((¬ b ∨ e) ∨ f)) ∧ (¬ c ∨ ¬ e)) ∧ (¬ c ∨ ¬ f)) ∧ ((¬ b ∨ g) ∨ h)) ∧ (¬ d ∨ ¬ g)) ∧ (¬ d ∨ ¬ h)) ⇒ ⊥)
                            assume {Γ = Γ} $  -- Γ ⊢ ¬ (((((((((¬ a ∧ (a ∨ b)) ∧ (c ∨ d)) ∧ ((¬ b ∨ e) ∨ f)) ∧ (¬ c ∨ ¬ e)) ∧ (¬ c ∨ ¬ f)) ∧ ((¬ b ∨ g) ∨ h)) ∧ (¬ d ∨ ¬ g)) ∧ (¬ d ∨ ¬ h)) ⇒ ⊥)
                              atp-neg subgoal₁₃
                  )
              )
          )
          (
                      id -- resolve 4.
              (
                              atp-canonicalize $  -- Γ ⊢ ({ e f : Set} → e ∨ f)
                  atp-simplify $  -- Γ ⊢ (e ∨ f)
                    ∧-intro
                      (
                      ∧-proj₁ $ -- 1: (((((((¬ a ∧ (¬ c ∨ ¬ e)) ∧ (¬ c ∨ ¬ f)) ∧ (¬ d ∨ ¬ g)) ∧ (¬ d ∨ ¬ h)) ∧ (a ∨ b)) ∧ (c ∨ d)) ∧ ((¬ b ∨ e) ∨ f))
                        atp-canonicalize $  -- Γ ⊢ ((((((((¬ a ∧ (¬ c ∨ ¬ e)) ∧ (¬ c ∨ ¬ f)) ∧ (¬ d ∨ ¬ g)) ∧ (¬ d ∨ ¬ h)) ∧ (a ∨ b)) ∧ (c ∨ d)) ∧ ((¬ b ∨ e) ∨ f)) ∧ ((¬ b ∨ g) ∨ h))
                          atp-strip $  -- Γ ⊢ (((((((((¬ a ∧ (a ∨ b)) ∧ (c ∨ d)) ∧ ((¬ b ∨ e) ∨ f)) ∧ (¬ c ∨ ¬ e)) ∧ (¬ c ∨ ¬ f)) ∧ ((¬ b ∨ g) ∨ h)) ∧ (¬ d ∨ ¬ g)) ∧ (¬ d ∨ ¬ h)) ⇒ ⊥)
                            assume {Γ = Γ} $  -- Γ ⊢ ¬ (((((((((¬ a ∧ (a ∨ b)) ∧ (c ∨ d)) ∧ ((¬ b ∨ e) ∨ f)) ∧ (¬ c ∨ ¬ e)) ∧ (¬ c ∨ ¬ f)) ∧ ((¬ b ∨ g) ∨ h)) ∧ (¬ d ∨ ¬ g)) ∧ (¬ d ∨ ¬ h)) ⇒ ⊥)
                              atp-neg subgoal₁₃
                      )
                      (
                      atp-simplify $  -- Γ ⊢ b
                        ∧-intro
                          (
                          ∧-proj₁ $ -- 1: (((((((¬ a ∧ (¬ c ∨ ¬ e)) ∧ (¬ c ∨ ¬ f)) ∧ (¬ d ∨ ¬ g)) ∧ (¬ d ∨ ¬ h)) ∧ (a ∨ b)) ∧ (c ∨ d)) ∧ ((¬ b ∨ e) ∨ f))
                            atp-canonicalize $  -- Γ ⊢ ((((((((¬ a ∧ (¬ c ∨ ¬ e)) ∧ (¬ c ∨ ¬ f)) ∧ (¬ d ∨ ¬ g)) ∧ (¬ d ∨ ¬ h)) ∧ (a ∨ b)) ∧ (c ∨ d)) ∧ ((¬ b ∨ e) ∨ f)) ∧ ((¬ b ∨ g) ∨ h))
                              atp-strip $  -- Γ ⊢ (((((((((¬ a ∧ (a ∨ b)) ∧ (c ∨ d)) ∧ ((¬ b ∨ e) ∨ f)) ∧ (¬ c ∨ ¬ e)) ∧ (¬ c ∨ ¬ f)) ∧ ((¬ b ∨ g) ∨ h)) ∧ (¬ d ∨ ¬ g)) ∧ (¬ d ∨ ¬ h)) ⇒ ⊥)
                                assume {Γ = Γ} $  -- Γ ⊢ ¬ (((((((((¬ a ∧ (a ∨ b)) ∧ (c ∨ d)) ∧ ((¬ b ∨ e) ∨ f)) ∧ (¬ c ∨ ¬ e)) ∧ (¬ c ∨ ¬ f)) ∧ ((¬ b ∨ g) ∨ h)) ∧ (¬ d ∨ ¬ g)) ∧ (¬ d ∨ ¬ h)) ⇒ ⊥)
                                  atp-neg subgoal₁₃
                          )
                          (
                          ∧-proj₁ $ -- 1: (((((((¬ a ∧ (¬ c ∨ ¬ e)) ∧ (¬ c ∨ ¬ f)) ∧ (¬ d ∨ ¬ g)) ∧ (¬ d ∨ ¬ h)) ∧ (a ∨ b)) ∧ (c ∨ d)) ∧ ((¬ b ∨ e) ∨ f))
                            atp-canonicalize $  -- Γ ⊢ ((((((((¬ a ∧ (¬ c ∨ ¬ e)) ∧ (¬ c ∨ ¬ f)) ∧ (¬ d ∨ ¬ g)) ∧ (¬ d ∨ ¬ h)) ∧ (a ∨ b)) ∧ (c ∨ d)) ∧ ((¬ b ∨ e) ∨ f)) ∧ ((¬ b ∨ g) ∨ h))
                              atp-strip $  -- Γ ⊢ (((((((((¬ a ∧ (a ∨ b)) ∧ (c ∨ d)) ∧ ((¬ b ∨ e) ∨ f)) ∧ (¬ c ∨ ¬ e)) ∧ (¬ c ∨ ¬ f)) ∧ ((¬ b ∨ g) ∨ h)) ∧ (¬ d ∨ ¬ g)) ∧ (¬ d ∨ ¬ h)) ⇒ ⊥)
                                assume {Γ = Γ} $  -- Γ ⊢ ¬ (((((((((¬ a ∧ (a ∨ b)) ∧ (c ∨ d)) ∧ ((¬ b ∨ e) ∨ f)) ∧ (¬ c ∨ ¬ e)) ∧ (¬ c ∨ ¬ f)) ∧ ((¬ b ∨ g) ∨ h)) ∧ (¬ d ∨ ¬ g)) ∧ (¬ d ∨ ¬ h)) ⇒ ⊥)
                                  atp-neg subgoal₁₃
                          )
                      )
              )
              (
                              atp-canonicalize $  -- Γ ⊢ ({ c f : Set} → ¬ c ∨ ¬ f)
                  ∧-proj₁ $ -- 1: (((((((¬ a ∧ (¬ c ∨ ¬ e)) ∧ (¬ c ∨ ¬ f)) ∧ (¬ d ∨ ¬ g)) ∧ (¬ d ∨ ¬ h)) ∧ (a ∨ b)) ∧ (c ∨ d)) ∧ ((¬ b ∨ e) ∨ f))
                    atp-canonicalize $  -- Γ ⊢ ((((((((¬ a ∧ (¬ c ∨ ¬ e)) ∧ (¬ c ∨ ¬ f)) ∧ (¬ d ∨ ¬ g)) ∧ (¬ d ∨ ¬ h)) ∧ (a ∨ b)) ∧ (c ∨ d)) ∧ ((¬ b ∨ e) ∨ f)) ∧ ((¬ b ∨ g) ∨ h))
                      atp-strip $  -- Γ ⊢ (((((((((¬ a ∧ (a ∨ b)) ∧ (c ∨ d)) ∧ ((¬ b ∨ e) ∨ f)) ∧ (¬ c ∨ ¬ e)) ∧ (¬ c ∨ ¬ f)) ∧ ((¬ b ∨ g) ∨ h)) ∧ (¬ d ∨ ¬ g)) ∧ (¬ d ∨ ¬ h)) ⇒ ⊥)
                        assume {Γ = Γ} $  -- Γ ⊢ ¬ (((((((((¬ a ∧ (a ∨ b)) ∧ (c ∨ d)) ∧ ((¬ b ∨ e) ∨ f)) ∧ (¬ c ∨ ¬ e)) ∧ (¬ c ∨ ¬ f)) ∧ ((¬ b ∨ g) ∨ h)) ∧ (¬ d ∨ ¬ g)) ∧ (¬ d ∨ ¬ h)) ⇒ ⊥)
                          atp-neg subgoal₁₃
              )
          )
      )
      (
              atp-canonicalize $  -- Γ ⊢ ({ c e : Set} → ¬ c ∨ ¬ e)
          ∧-proj₁ $ -- 1: (((((((¬ a ∧ (¬ c ∨ ¬ e)) ∧ (¬ c ∨ ¬ f)) ∧ (¬ d ∨ ¬ g)) ∧ (¬ d ∨ ¬ h)) ∧ (a ∨ b)) ∧ (c ∨ d)) ∧ ((¬ b ∨ e) ∨ f))
            atp-canonicalize $  -- Γ ⊢ ((((((((¬ a ∧ (¬ c ∨ ¬ e)) ∧ (¬ c ∨ ¬ f)) ∧ (¬ d ∨ ¬ g)) ∧ (¬ d ∨ ¬ h)) ∧ (a ∨ b)) ∧ (c ∨ d)) ∧ ((¬ b ∨ e) ∨ f)) ∧ ((¬ b ∨ g) ∨ h))
              atp-strip $  -- Γ ⊢ (((((((((¬ a ∧ (a ∨ b)) ∧ (c ∨ d)) ∧ ((¬ b ∨ e) ∨ f)) ∧ (¬ c ∨ ¬ e)) ∧ (¬ c ∨ ¬ f)) ∧ ((¬ b ∨ g) ∨ h)) ∧ (¬ d ∨ ¬ g)) ∧ (¬ d ∨ ¬ h)) ⇒ ⊥)
                assume {Γ = Γ} $  -- Γ ⊢ ¬ (((((((((¬ a ∧ (a ∨ b)) ∧ (c ∨ d)) ∧ ((¬ b ∨ e) ∨ f)) ∧ (¬ c ∨ ¬ e)) ∧ (¬ c ∨ ¬ f)) ∧ ((¬ b ∨ g) ∨ h)) ∧ (¬ d ∨ ¬ g)) ∧ (¬ d ∨ ¬ h)) ⇒ ⊥)
                  atp-neg subgoal₁₃
      )

proof₁₄ : Γ ⊢ subgoal₁₄
proof₁₄ =
  RAA $
    id -- resolve 4.
      (
              id -- resolve 4.
          (
                      atp-canonicalize $  -- Γ ⊢ ({ c d : Set} → c ∨ d)
              ∧-proj₁ $ -- 1: (((((((¬ a ∧ (¬ c ∨ ¬ e)) ∧ (¬ c ∨ ¬ f)) ∧ (¬ d ∨ ¬ g)) ∧ (¬ d ∨ ¬ h)) ∧ (a ∨ b)) ∧ (c ∨ d)) ∧ ((¬ b ∨ e) ∨ f))
                atp-canonicalize $  -- Γ ⊢ ((((((((¬ a ∧ (¬ c ∨ ¬ e)) ∧ (¬ c ∨ ¬ f)) ∧ (¬ d ∨ ¬ g)) ∧ (¬ d ∨ ¬ h)) ∧ (a ∨ b)) ∧ (c ∨ d)) ∧ ((¬ b ∨ e) ∨ f)) ∧ ((¬ b ∨ g) ∨ h))
                  atp-strip $  -- Γ ⊢ (((((((((¬ a ∧ (a ∨ b)) ∧ (c ∨ d)) ∧ ((¬ b ∨ e) ∨ f)) ∧ (¬ c ∨ ¬ e)) ∧ (¬ c ∨ ¬ f)) ∧ ((¬ b ∨ g) ∨ h)) ∧ (¬ d ∨ ¬ g)) ∧ (¬ d ∨ ¬ h)) ⇒ ⊥)
                    assume {Γ = Γ} $  -- Γ ⊢ ¬ (((((((((¬ a ∧ (a ∨ b)) ∧ (c ∨ d)) ∧ ((¬ b ∨ e) ∨ f)) ∧ (¬ c ∨ ¬ e)) ∧ (¬ c ∨ ¬ f)) ∧ ((¬ b ∨ g) ∨ h)) ∧ (¬ d ∨ ¬ g)) ∧ (¬ d ∨ ¬ h)) ⇒ ⊥)
                      atp-neg subgoal₁₄
          )
          (
                      id -- resolve 4.
              (
                              id -- resolve 4.
                  (
                                      atp-canonicalize $  -- Γ ⊢ ({ c d : Set} → c ∨ d)
                      ∧-proj₁ $ -- 1: (((((((¬ a ∧ (¬ c ∨ ¬ e)) ∧ (¬ c ∨ ¬ f)) ∧ (¬ d ∨ ¬ g)) ∧ (¬ d ∨ ¬ h)) ∧ (a ∨ b)) ∧ (c ∨ d)) ∧ ((¬ b ∨ e) ∨ f))
                        atp-canonicalize $  -- Γ ⊢ ((((((((¬ a ∧ (¬ c ∨ ¬ e)) ∧ (¬ c ∨ ¬ f)) ∧ (¬ d ∨ ¬ g)) ∧ (¬ d ∨ ¬ h)) ∧ (a ∨ b)) ∧ (c ∨ d)) ∧ ((¬ b ∨ e) ∨ f)) ∧ ((¬ b ∨ g) ∨ h))
                          atp-strip $  -- Γ ⊢ (((((((((¬ a ∧ (a ∨ b)) ∧ (c ∨ d)) ∧ ((¬ b ∨ e) ∨ f)) ∧ (¬ c ∨ ¬ e)) ∧ (¬ c ∨ ¬ f)) ∧ ((¬ b ∨ g) ∨ h)) ∧ (¬ d ∨ ¬ g)) ∧ (¬ d ∨ ¬ h)) ⇒ ⊥)
                            assume {Γ = Γ} $  -- Γ ⊢ ¬ (((((((((¬ a ∧ (a ∨ b)) ∧ (c ∨ d)) ∧ ((¬ b ∨ e) ∨ f)) ∧ (¬ c ∨ ¬ e)) ∧ (¬ c ∨ ¬ f)) ∧ ((¬ b ∨ g) ∨ h)) ∧ (¬ d ∨ ¬ g)) ∧ (¬ d ∨ ¬ h)) ⇒ ⊥)
                              atp-neg subgoal₁₄
                  )
                  (
                                      id -- resolve 4.
                      (
                                              atp-canonicalize $  -- Γ ⊢ ({ g h : Set} → g ∨ h)
                          atp-simplify $  -- Γ ⊢ (g ∨ h)
                            ∧-intro
                              (
                              ∧-proj₂ $ -- (((¬ b ∨ g) ∨ h) ≟ ((¬ b ∨ g) ∨ h))
                                atp-canonicalize $  -- Γ ⊢ ((((((((¬ a ∧ (¬ c ∨ ¬ e)) ∧ (¬ c ∨ ¬ f)) ∧ (¬ d ∨ ¬ g)) ∧ (¬ d ∨ ¬ h)) ∧ (a ∨ b)) ∧ (c ∨ d)) ∧ ((¬ b ∨ e) ∨ f)) ∧ ((¬ b ∨ g) ∨ h))
                                  atp-strip $  -- Γ ⊢ (((((((((¬ a ∧ (a ∨ b)) ∧ (c ∨ d)) ∧ ((¬ b ∨ e) ∨ f)) ∧ (¬ c ∨ ¬ e)) ∧ (¬ c ∨ ¬ f)) ∧ ((¬ b ∨ g) ∨ h)) ∧ (¬ d ∨ ¬ g)) ∧ (¬ d ∨ ¬ h)) ⇒ ⊥)
                                    assume {Γ = Γ} $  -- Γ ⊢ ¬ (((((((((¬ a ∧ (a ∨ b)) ∧ (c ∨ d)) ∧ ((¬ b ∨ e) ∨ f)) ∧ (¬ c ∨ ¬ e)) ∧ (¬ c ∨ ¬ f)) ∧ ((¬ b ∨ g) ∨ h)) ∧ (¬ d ∨ ¬ g)) ∧ (¬ d ∨ ¬ h)) ⇒ ⊥)
                                      atp-neg subgoal₁₄
                              )
                              (
                              atp-simplify $  -- Γ ⊢ b
                                ∧-intro
                                  (
                                  ∧-proj₁ $ -- 1: (((((((¬ a ∧ (¬ c ∨ ¬ e)) ∧ (¬ c ∨ ¬ f)) ∧ (¬ d ∨ ¬ g)) ∧ (¬ d ∨ ¬ h)) ∧ (a ∨ b)) ∧ (c ∨ d)) ∧ ((¬ b ∨ e) ∨ f))
                                    atp-canonicalize $  -- Γ ⊢ ((((((((¬ a ∧ (¬ c ∨ ¬ e)) ∧ (¬ c ∨ ¬ f)) ∧ (¬ d ∨ ¬ g)) ∧ (¬ d ∨ ¬ h)) ∧ (a ∨ b)) ∧ (c ∨ d)) ∧ ((¬ b ∨ e) ∨ f)) ∧ ((¬ b ∨ g) ∨ h))
                                      atp-strip $  -- Γ ⊢ (((((((((¬ a ∧ (a ∨ b)) ∧ (c ∨ d)) ∧ ((¬ b ∨ e) ∨ f)) ∧ (¬ c ∨ ¬ e)) ∧ (¬ c ∨ ¬ f)) ∧ ((¬ b ∨ g) ∨ h)) ∧ (¬ d ∨ ¬ g)) ∧ (¬ d ∨ ¬ h)) ⇒ ⊥)
                                        assume {Γ = Γ} $  -- Γ ⊢ ¬ (((((((((¬ a ∧ (a ∨ b)) ∧ (c ∨ d)) ∧ ((¬ b ∨ e) ∨ f)) ∧ (¬ c ∨ ¬ e)) ∧ (¬ c ∨ ¬ f)) ∧ ((¬ b ∨ g) ∨ h)) ∧ (¬ d ∨ ¬ g)) ∧ (¬ d ∨ ¬ h)) ⇒ ⊥)
                                          atp-neg subgoal₁₄
                                  )
                                  (
                                  ∧-proj₁ $ -- 1: (((((((¬ a ∧ (¬ c ∨ ¬ e)) ∧ (¬ c ∨ ¬ f)) ∧ (¬ d ∨ ¬ g)) ∧ (¬ d ∨ ¬ h)) ∧ (a ∨ b)) ∧ (c ∨ d)) ∧ ((¬ b ∨ e) ∨ f))
                                    atp-canonicalize $  -- Γ ⊢ ((((((((¬ a ∧ (¬ c ∨ ¬ e)) ∧ (¬ c ∨ ¬ f)) ∧ (¬ d ∨ ¬ g)) ∧ (¬ d ∨ ¬ h)) ∧ (a ∨ b)) ∧ (c ∨ d)) ∧ ((¬ b ∨ e) ∨ f)) ∧ ((¬ b ∨ g) ∨ h))
                                      atp-strip $  -- Γ ⊢ (((((((((¬ a ∧ (a ∨ b)) ∧ (c ∨ d)) ∧ ((¬ b ∨ e) ∨ f)) ∧ (¬ c ∨ ¬ e)) ∧ (¬ c ∨ ¬ f)) ∧ ((¬ b ∨ g) ∨ h)) ∧ (¬ d ∨ ¬ g)) ∧ (¬ d ∨ ¬ h)) ⇒ ⊥)
                                        assume {Γ = Γ} $  -- Γ ⊢ ¬ (((((((((¬ a ∧ (a ∨ b)) ∧ (c ∨ d)) ∧ ((¬ b ∨ e) ∨ f)) ∧ (¬ c ∨ ¬ e)) ∧ (¬ c ∨ ¬ f)) ∧ ((¬ b ∨ g) ∨ h)) ∧ (¬ d ∨ ¬ g)) ∧ (¬ d ∨ ¬ h)) ⇒ ⊥)
                                          atp-neg subgoal₁₄
                                  )
                              )
                      )
                      (
                                              atp-canonicalize $  -- Γ ⊢ ({ d h : Set} → ¬ d ∨ ¬ h)
                          ∧-proj₁ $ -- 1: (((((((¬ a ∧ (¬ c ∨ ¬ e)) ∧ (¬ c ∨ ¬ f)) ∧ (¬ d ∨ ¬ g)) ∧ (¬ d ∨ ¬ h)) ∧ (a ∨ b)) ∧ (c ∨ d)) ∧ ((¬ b ∨ e) ∨ f))
                            atp-canonicalize $  -- Γ ⊢ ((((((((¬ a ∧ (¬ c ∨ ¬ e)) ∧ (¬ c ∨ ¬ f)) ∧ (¬ d ∨ ¬ g)) ∧ (¬ d ∨ ¬ h)) ∧ (a ∨ b)) ∧ (c ∨ d)) ∧ ((¬ b ∨ e) ∨ f)) ∧ ((¬ b ∨ g) ∨ h))
                              atp-strip $  -- Γ ⊢ (((((((((¬ a ∧ (a ∨ b)) ∧ (c ∨ d)) ∧ ((¬ b ∨ e) ∨ f)) ∧ (¬ c ∨ ¬ e)) ∧ (¬ c ∨ ¬ f)) ∧ ((¬ b ∨ g) ∨ h)) ∧ (¬ d ∨ ¬ g)) ∧ (¬ d ∨ ¬ h)) ⇒ ⊥)
                                assume {Γ = Γ} $  -- Γ ⊢ ¬ (((((((((¬ a ∧ (a ∨ b)) ∧ (c ∨ d)) ∧ ((¬ b ∨ e) ∨ f)) ∧ (¬ c ∨ ¬ e)) ∧ (¬ c ∨ ¬ f)) ∧ ((¬ b ∨ g) ∨ h)) ∧ (¬ d ∨ ¬ g)) ∧ (¬ d ∨ ¬ h)) ⇒ ⊥)
                                  atp-neg subgoal₁₄
                      )
                  )
              )
              (
                              atp-canonicalize $  -- Γ ⊢ ({ d g : Set} → ¬ d ∨ ¬ g)
                  ∧-proj₁ $ -- 1: (((((((¬ a ∧ (¬ c ∨ ¬ e)) ∧ (¬ c ∨ ¬ f)) ∧ (¬ d ∨ ¬ g)) ∧ (¬ d ∨ ¬ h)) ∧ (a ∨ b)) ∧ (c ∨ d)) ∧ ((¬ b ∨ e) ∨ f))
                    atp-canonicalize $  -- Γ ⊢ ((((((((¬ a ∧ (¬ c ∨ ¬ e)) ∧ (¬ c ∨ ¬ f)) ∧ (¬ d ∨ ¬ g)) ∧ (¬ d ∨ ¬ h)) ∧ (a ∨ b)) ∧ (c ∨ d)) ∧ ((¬ b ∨ e) ∨ f)) ∧ ((¬ b ∨ g) ∨ h))
                      atp-strip $  -- Γ ⊢ (((((((((¬ a ∧ (a ∨ b)) ∧ (c ∨ d)) ∧ ((¬ b ∨ e) ∨ f)) ∧ (¬ c ∨ ¬ e)) ∧ (¬ c ∨ ¬ f)) ∧ ((¬ b ∨ g) ∨ h)) ∧ (¬ d ∨ ¬ g)) ∧ (¬ d ∨ ¬ h)) ⇒ ⊥)
                        assume {Γ = Γ} $  -- Γ ⊢ ¬ (((((((((¬ a ∧ (a ∨ b)) ∧ (c ∨ d)) ∧ ((¬ b ∨ e) ∨ f)) ∧ (¬ c ∨ ¬ e)) ∧ (¬ c ∨ ¬ f)) ∧ ((¬ b ∨ g) ∨ h)) ∧ (¬ d ∨ ¬ g)) ∧ (¬ d ∨ ¬ h)) ⇒ ⊥)
                          atp-neg subgoal₁₄
              )
          )
      )
      (
              id -- resolve 4.
          (
                      id -- resolve 4.
              (
                              id -- resolve 4.
                  (
                                      atp-canonicalize $  -- Γ ⊢ ({ c d : Set} → c ∨ d)
                      ∧-proj₁ $ -- 1: (((((((¬ a ∧ (¬ c ∨ ¬ e)) ∧ (¬ c ∨ ¬ f)) ∧ (¬ d ∨ ¬ g)) ∧ (¬ d ∨ ¬ h)) ∧ (a ∨ b)) ∧ (c ∨ d)) ∧ ((¬ b ∨ e) ∨ f))
                        atp-canonicalize $  -- Γ ⊢ ((((((((¬ a ∧ (¬ c ∨ ¬ e)) ∧ (¬ c ∨ ¬ f)) ∧ (¬ d ∨ ¬ g)) ∧ (¬ d ∨ ¬ h)) ∧ (a ∨ b)) ∧ (c ∨ d)) ∧ ((¬ b ∨ e) ∨ f)) ∧ ((¬ b ∨ g) ∨ h))
                          atp-strip $  -- Γ ⊢ (((((((((¬ a ∧ (a ∨ b)) ∧ (c ∨ d)) ∧ ((¬ b ∨ e) ∨ f)) ∧ (¬ c ∨ ¬ e)) ∧ (¬ c ∨ ¬ f)) ∧ ((¬ b ∨ g) ∨ h)) ∧ (¬ d ∨ ¬ g)) ∧ (¬ d ∨ ¬ h)) ⇒ ⊥)
                            assume {Γ = Γ} $  -- Γ ⊢ ¬ (((((((((¬ a ∧ (a ∨ b)) ∧ (c ∨ d)) ∧ ((¬ b ∨ e) ∨ f)) ∧ (¬ c ∨ ¬ e)) ∧ (¬ c ∨ ¬ f)) ∧ ((¬ b ∨ g) ∨ h)) ∧ (¬ d ∨ ¬ g)) ∧ (¬ d ∨ ¬ h)) ⇒ ⊥)
                              atp-neg subgoal₁₄
                  )
                  (
                                      id -- resolve 4.
                      (
                                              id -- resolve 4.
                          (
                                                      atp-canonicalize $  -- Γ ⊢ ({ c d : Set} → c ∨ d)
                              ∧-proj₁ $ -- 1: (((((((¬ a ∧ (¬ c ∨ ¬ e)) ∧ (¬ c ∨ ¬ f)) ∧ (¬ d ∨ ¬ g)) ∧ (¬ d ∨ ¬ h)) ∧ (a ∨ b)) ∧ (c ∨ d)) ∧ ((¬ b ∨ e) ∨ f))
                                atp-canonicalize $  -- Γ ⊢ ((((((((¬ a ∧ (¬ c ∨ ¬ e)) ∧ (¬ c ∨ ¬ f)) ∧ (¬ d ∨ ¬ g)) ∧ (¬ d ∨ ¬ h)) ∧ (a ∨ b)) ∧ (c ∨ d)) ∧ ((¬ b ∨ e) ∨ f)) ∧ ((¬ b ∨ g) ∨ h))
                                  atp-strip $  -- Γ ⊢ (((((((((¬ a ∧ (a ∨ b)) ∧ (c ∨ d)) ∧ ((¬ b ∨ e) ∨ f)) ∧ (¬ c ∨ ¬ e)) ∧ (¬ c ∨ ¬ f)) ∧ ((¬ b ∨ g) ∨ h)) ∧ (¬ d ∨ ¬ g)) ∧ (¬ d ∨ ¬ h)) ⇒ ⊥)
                                    assume {Γ = Γ} $  -- Γ ⊢ ¬ (((((((((¬ a ∧ (a ∨ b)) ∧ (c ∨ d)) ∧ ((¬ b ∨ e) ∨ f)) ∧ (¬ c ∨ ¬ e)) ∧ (¬ c ∨ ¬ f)) ∧ ((¬ b ∨ g) ∨ h)) ∧ (¬ d ∨ ¬ g)) ∧ (¬ d ∨ ¬ h)) ⇒ ⊥)
                                      atp-neg subgoal₁₄
                          )
                          (
                                                      id -- resolve 4.
                              (
                                                              atp-canonicalize $  -- Γ ⊢ ({ g h : Set} → g ∨ h)
                                  atp-simplify $  -- Γ ⊢ (g ∨ h)
                                    ∧-intro
                                      (
                                      ∧-proj₂ $ -- (((¬ b ∨ g) ∨ h) ≟ ((¬ b ∨ g) ∨ h))
                                        atp-canonicalize $  -- Γ ⊢ ((((((((¬ a ∧ (¬ c ∨ ¬ e)) ∧ (¬ c ∨ ¬ f)) ∧ (¬ d ∨ ¬ g)) ∧ (¬ d ∨ ¬ h)) ∧ (a ∨ b)) ∧ (c ∨ d)) ∧ ((¬ b ∨ e) ∨ f)) ∧ ((¬ b ∨ g) ∨ h))
                                          atp-strip $  -- Γ ⊢ (((((((((¬ a ∧ (a ∨ b)) ∧ (c ∨ d)) ∧ ((¬ b ∨ e) ∨ f)) ∧ (¬ c ∨ ¬ e)) ∧ (¬ c ∨ ¬ f)) ∧ ((¬ b ∨ g) ∨ h)) ∧ (¬ d ∨ ¬ g)) ∧ (¬ d ∨ ¬ h)) ⇒ ⊥)
                                            assume {Γ = Γ} $  -- Γ ⊢ ¬ (((((((((¬ a ∧ (a ∨ b)) ∧ (c ∨ d)) ∧ ((¬ b ∨ e) ∨ f)) ∧ (¬ c ∨ ¬ e)) ∧ (¬ c ∨ ¬ f)) ∧ ((¬ b ∨ g) ∨ h)) ∧ (¬ d ∨ ¬ g)) ∧ (¬ d ∨ ¬ h)) ⇒ ⊥)
                                              atp-neg subgoal₁₄
                                      )
                                      (
                                      atp-simplify $  -- Γ ⊢ b
                                        ∧-intro
                                          (
                                          ∧-proj₁ $ -- 1: (((((((¬ a ∧ (¬ c ∨ ¬ e)) ∧ (¬ c ∨ ¬ f)) ∧ (¬ d ∨ ¬ g)) ∧ (¬ d ∨ ¬ h)) ∧ (a ∨ b)) ∧ (c ∨ d)) ∧ ((¬ b ∨ e) ∨ f))
                                            atp-canonicalize $  -- Γ ⊢ ((((((((¬ a ∧ (¬ c ∨ ¬ e)) ∧ (¬ c ∨ ¬ f)) ∧ (¬ d ∨ ¬ g)) ∧ (¬ d ∨ ¬ h)) ∧ (a ∨ b)) ∧ (c ∨ d)) ∧ ((¬ b ∨ e) ∨ f)) ∧ ((¬ b ∨ g) ∨ h))
                                              atp-strip $  -- Γ ⊢ (((((((((¬ a ∧ (a ∨ b)) ∧ (c ∨ d)) ∧ ((¬ b ∨ e) ∨ f)) ∧ (¬ c ∨ ¬ e)) ∧ (¬ c ∨ ¬ f)) ∧ ((¬ b ∨ g) ∨ h)) ∧ (¬ d ∨ ¬ g)) ∧ (¬ d ∨ ¬ h)) ⇒ ⊥)
                                                assume {Γ = Γ} $  -- Γ ⊢ ¬ (((((((((¬ a ∧ (a ∨ b)) ∧ (c ∨ d)) ∧ ((¬ b ∨ e) ∨ f)) ∧ (¬ c ∨ ¬ e)) ∧ (¬ c ∨ ¬ f)) ∧ ((¬ b ∨ g) ∨ h)) ∧ (¬ d ∨ ¬ g)) ∧ (¬ d ∨ ¬ h)) ⇒ ⊥)
                                                  atp-neg subgoal₁₄
                                          )
                                          (
                                          ∧-proj₁ $ -- 1: (((((((¬ a ∧ (¬ c ∨ ¬ e)) ∧ (¬ c ∨ ¬ f)) ∧ (¬ d ∨ ¬ g)) ∧ (¬ d ∨ ¬ h)) ∧ (a ∨ b)) ∧ (c ∨ d)) ∧ ((¬ b ∨ e) ∨ f))
                                            atp-canonicalize $  -- Γ ⊢ ((((((((¬ a ∧ (¬ c ∨ ¬ e)) ∧ (¬ c ∨ ¬ f)) ∧ (¬ d ∨ ¬ g)) ∧ (¬ d ∨ ¬ h)) ∧ (a ∨ b)) ∧ (c ∨ d)) ∧ ((¬ b ∨ e) ∨ f)) ∧ ((¬ b ∨ g) ∨ h))
                                              atp-strip $  -- Γ ⊢ (((((((((¬ a ∧ (a ∨ b)) ∧ (c ∨ d)) ∧ ((¬ b ∨ e) ∨ f)) ∧ (¬ c ∨ ¬ e)) ∧ (¬ c ∨ ¬ f)) ∧ ((¬ b ∨ g) ∨ h)) ∧ (¬ d ∨ ¬ g)) ∧ (¬ d ∨ ¬ h)) ⇒ ⊥)
                                                assume {Γ = Γ} $  -- Γ ⊢ ¬ (((((((((¬ a ∧ (a ∨ b)) ∧ (c ∨ d)) ∧ ((¬ b ∨ e) ∨ f)) ∧ (¬ c ∨ ¬ e)) ∧ (¬ c ∨ ¬ f)) ∧ ((¬ b ∨ g) ∨ h)) ∧ (¬ d ∨ ¬ g)) ∧ (¬ d ∨ ¬ h)) ⇒ ⊥)
                                                  atp-neg subgoal₁₄
                                          )
                                      )
                              )
                              (
                                                              atp-canonicalize $  -- Γ ⊢ ({ d h : Set} → ¬ d ∨ ¬ h)
                                  ∧-proj₁ $ -- 1: (((((((¬ a ∧ (¬ c ∨ ¬ e)) ∧ (¬ c ∨ ¬ f)) ∧ (¬ d ∨ ¬ g)) ∧ (¬ d ∨ ¬ h)) ∧ (a ∨ b)) ∧ (c ∨ d)) ∧ ((¬ b ∨ e) ∨ f))
                                    atp-canonicalize $  -- Γ ⊢ ((((((((¬ a ∧ (¬ c ∨ ¬ e)) ∧ (¬ c ∨ ¬ f)) ∧ (¬ d ∨ ¬ g)) ∧ (¬ d ∨ ¬ h)) ∧ (a ∨ b)) ∧ (c ∨ d)) ∧ ((¬ b ∨ e) ∨ f)) ∧ ((¬ b ∨ g) ∨ h))
                                      atp-strip $  -- Γ ⊢ (((((((((¬ a ∧ (a ∨ b)) ∧ (c ∨ d)) ∧ ((¬ b ∨ e) ∨ f)) ∧ (¬ c ∨ ¬ e)) ∧ (¬ c ∨ ¬ f)) ∧ ((¬ b ∨ g) ∨ h)) ∧ (¬ d ∨ ¬ g)) ∧ (¬ d ∨ ¬ h)) ⇒ ⊥)
                                        assume {Γ = Γ} $  -- Γ ⊢ ¬ (((((((((¬ a ∧ (a ∨ b)) ∧ (c ∨ d)) ∧ ((¬ b ∨ e) ∨ f)) ∧ (¬ c ∨ ¬ e)) ∧ (¬ c ∨ ¬ f)) ∧ ((¬ b ∨ g) ∨ h)) ∧ (¬ d ∨ ¬ g)) ∧ (¬ d ∨ ¬ h)) ⇒ ⊥)
                                          atp-neg subgoal₁₄
                              )
                          )
                      )
                      (
                                              atp-canonicalize $  -- Γ ⊢ ({ d g : Set} → ¬ d ∨ ¬ g)
                          ∧-proj₁ $ -- 1: (((((((¬ a ∧ (¬ c ∨ ¬ e)) ∧ (¬ c ∨ ¬ f)) ∧ (¬ d ∨ ¬ g)) ∧ (¬ d ∨ ¬ h)) ∧ (a ∨ b)) ∧ (c ∨ d)) ∧ ((¬ b ∨ e) ∨ f))
                            atp-canonicalize $  -- Γ ⊢ ((((((((¬ a ∧ (¬ c ∨ ¬ e)) ∧ (¬ c ∨ ¬ f)) ∧ (¬ d ∨ ¬ g)) ∧ (¬ d ∨ ¬ h)) ∧ (a ∨ b)) ∧ (c ∨ d)) ∧ ((¬ b ∨ e) ∨ f)) ∧ ((¬ b ∨ g) ∨ h))
                              atp-strip $  -- Γ ⊢ (((((((((¬ a ∧ (a ∨ b)) ∧ (c ∨ d)) ∧ ((¬ b ∨ e) ∨ f)) ∧ (¬ c ∨ ¬ e)) ∧ (¬ c ∨ ¬ f)) ∧ ((¬ b ∨ g) ∨ h)) ∧ (¬ d ∨ ¬ g)) ∧ (¬ d ∨ ¬ h)) ⇒ ⊥)
                                assume {Γ = Γ} $  -- Γ ⊢ ¬ (((((((((¬ a ∧ (a ∨ b)) ∧ (c ∨ d)) ∧ ((¬ b ∨ e) ∨ f)) ∧ (¬ c ∨ ¬ e)) ∧ (¬ c ∨ ¬ f)) ∧ ((¬ b ∨ g) ∨ h)) ∧ (¬ d ∨ ¬ g)) ∧ (¬ d ∨ ¬ h)) ⇒ ⊥)
                                  atp-neg subgoal₁₄
                      )
                  )
              )
              (
                              id -- resolve 4.
                  (
                                      atp-canonicalize $  -- Γ ⊢ ({ e f : Set} → e ∨ f)
                      atp-simplify $  -- Γ ⊢ (e ∨ f)
                        ∧-intro
                          (
                          ∧-proj₁ $ -- 1: (((((((¬ a ∧ (¬ c ∨ ¬ e)) ∧ (¬ c ∨ ¬ f)) ∧ (¬ d ∨ ¬ g)) ∧ (¬ d ∨ ¬ h)) ∧ (a ∨ b)) ∧ (c ∨ d)) ∧ ((¬ b ∨ e) ∨ f))
                            atp-canonicalize $  -- Γ ⊢ ((((((((¬ a ∧ (¬ c ∨ ¬ e)) ∧ (¬ c ∨ ¬ f)) ∧ (¬ d ∨ ¬ g)) ∧ (¬ d ∨ ¬ h)) ∧ (a ∨ b)) ∧ (c ∨ d)) ∧ ((¬ b ∨ e) ∨ f)) ∧ ((¬ b ∨ g) ∨ h))
                              atp-strip $  -- Γ ⊢ (((((((((¬ a ∧ (a ∨ b)) ∧ (c ∨ d)) ∧ ((¬ b ∨ e) ∨ f)) ∧ (¬ c ∨ ¬ e)) ∧ (¬ c ∨ ¬ f)) ∧ ((¬ b ∨ g) ∨ h)) ∧ (¬ d ∨ ¬ g)) ∧ (¬ d ∨ ¬ h)) ⇒ ⊥)
                                assume {Γ = Γ} $  -- Γ ⊢ ¬ (((((((((¬ a ∧ (a ∨ b)) ∧ (c ∨ d)) ∧ ((¬ b ∨ e) ∨ f)) ∧ (¬ c ∨ ¬ e)) ∧ (¬ c ∨ ¬ f)) ∧ ((¬ b ∨ g) ∨ h)) ∧ (¬ d ∨ ¬ g)) ∧ (¬ d ∨ ¬ h)) ⇒ ⊥)
                                  atp-neg subgoal₁₄
                          )
                          (
                          atp-simplify $  -- Γ ⊢ b
                            ∧-intro
                              (
                              ∧-proj₁ $ -- 1: (((((((¬ a ∧ (¬ c ∨ ¬ e)) ∧ (¬ c ∨ ¬ f)) ∧ (¬ d ∨ ¬ g)) ∧ (¬ d ∨ ¬ h)) ∧ (a ∨ b)) ∧ (c ∨ d)) ∧ ((¬ b ∨ e) ∨ f))
                                atp-canonicalize $  -- Γ ⊢ ((((((((¬ a ∧ (¬ c ∨ ¬ e)) ∧ (¬ c ∨ ¬ f)) ∧ (¬ d ∨ ¬ g)) ∧ (¬ d ∨ ¬ h)) ∧ (a ∨ b)) ∧ (c ∨ d)) ∧ ((¬ b ∨ e) ∨ f)) ∧ ((¬ b ∨ g) ∨ h))
                                  atp-strip $  -- Γ ⊢ (((((((((¬ a ∧ (a ∨ b)) ∧ (c ∨ d)) ∧ ((¬ b ∨ e) ∨ f)) ∧ (¬ c ∨ ¬ e)) ∧ (¬ c ∨ ¬ f)) ∧ ((¬ b ∨ g) ∨ h)) ∧ (¬ d ∨ ¬ g)) ∧ (¬ d ∨ ¬ h)) ⇒ ⊥)
                                    assume {Γ = Γ} $  -- Γ ⊢ ¬ (((((((((¬ a ∧ (a ∨ b)) ∧ (c ∨ d)) ∧ ((¬ b ∨ e) ∨ f)) ∧ (¬ c ∨ ¬ e)) ∧ (¬ c ∨ ¬ f)) ∧ ((¬ b ∨ g) ∨ h)) ∧ (¬ d ∨ ¬ g)) ∧ (¬ d ∨ ¬ h)) ⇒ ⊥)
                                      atp-neg subgoal₁₄
                              )
                              (
                              ∧-proj₁ $ -- 1: (((((((¬ a ∧ (¬ c ∨ ¬ e)) ∧ (¬ c ∨ ¬ f)) ∧ (¬ d ∨ ¬ g)) ∧ (¬ d ∨ ¬ h)) ∧ (a ∨ b)) ∧ (c ∨ d)) ∧ ((¬ b ∨ e) ∨ f))
                                atp-canonicalize $  -- Γ ⊢ ((((((((¬ a ∧ (¬ c ∨ ¬ e)) ∧ (¬ c ∨ ¬ f)) ∧ (¬ d ∨ ¬ g)) ∧ (¬ d ∨ ¬ h)) ∧ (a ∨ b)) ∧ (c ∨ d)) ∧ ((¬ b ∨ e) ∨ f)) ∧ ((¬ b ∨ g) ∨ h))
                                  atp-strip $  -- Γ ⊢ (((((((((¬ a ∧ (a ∨ b)) ∧ (c ∨ d)) ∧ ((¬ b ∨ e) ∨ f)) ∧ (¬ c ∨ ¬ e)) ∧ (¬ c ∨ ¬ f)) ∧ ((¬ b ∨ g) ∨ h)) ∧ (¬ d ∨ ¬ g)) ∧ (¬ d ∨ ¬ h)) ⇒ ⊥)
                                    assume {Γ = Γ} $  -- Γ ⊢ ¬ (((((((((¬ a ∧ (a ∨ b)) ∧ (c ∨ d)) ∧ ((¬ b ∨ e) ∨ f)) ∧ (¬ c ∨ ¬ e)) ∧ (¬ c ∨ ¬ f)) ∧ ((¬ b ∨ g) ∨ h)) ∧ (¬ d ∨ ¬ g)) ∧ (¬ d ∨ ¬ h)) ⇒ ⊥)
                                      atp-neg subgoal₁₄
                              )
                          )
                  )
                  (
                                      atp-canonicalize $  -- Γ ⊢ ({ c f : Set} → ¬ c ∨ ¬ f)
                      ∧-proj₁ $ -- 1: (((((((¬ a ∧ (¬ c ∨ ¬ e)) ∧ (¬ c ∨ ¬ f)) ∧ (¬ d ∨ ¬ g)) ∧ (¬ d ∨ ¬ h)) ∧ (a ∨ b)) ∧ (c ∨ d)) ∧ ((¬ b ∨ e) ∨ f))
                        atp-canonicalize $  -- Γ ⊢ ((((((((¬ a ∧ (¬ c ∨ ¬ e)) ∧ (¬ c ∨ ¬ f)) ∧ (¬ d ∨ ¬ g)) ∧ (¬ d ∨ ¬ h)) ∧ (a ∨ b)) ∧ (c ∨ d)) ∧ ((¬ b ∨ e) ∨ f)) ∧ ((¬ b ∨ g) ∨ h))
                          atp-strip $  -- Γ ⊢ (((((((((¬ a ∧ (a ∨ b)) ∧ (c ∨ d)) ∧ ((¬ b ∨ e) ∨ f)) ∧ (¬ c ∨ ¬ e)) ∧ (¬ c ∨ ¬ f)) ∧ ((¬ b ∨ g) ∨ h)) ∧ (¬ d ∨ ¬ g)) ∧ (¬ d ∨ ¬ h)) ⇒ ⊥)
                            assume {Γ = Γ} $  -- Γ ⊢ ¬ (((((((((¬ a ∧ (a ∨ b)) ∧ (c ∨ d)) ∧ ((¬ b ∨ e) ∨ f)) ∧ (¬ c ∨ ¬ e)) ∧ (¬ c ∨ ¬ f)) ∧ ((¬ b ∨ g) ∨ h)) ∧ (¬ d ∨ ¬ g)) ∧ (¬ d ∨ ¬ h)) ⇒ ⊥)
                              atp-neg subgoal₁₄
                  )
              )
          )
          (
                      atp-canonicalize $  -- Γ ⊢ ({ c e : Set} → ¬ c ∨ ¬ e)
              ∧-proj₁ $ -- 1: (((((((¬ a ∧ (¬ c ∨ ¬ e)) ∧ (¬ c ∨ ¬ f)) ∧ (¬ d ∨ ¬ g)) ∧ (¬ d ∨ ¬ h)) ∧ (a ∨ b)) ∧ (c ∨ d)) ∧ ((¬ b ∨ e) ∨ f))
                atp-canonicalize $  -- Γ ⊢ ((((((((¬ a ∧ (¬ c ∨ ¬ e)) ∧ (¬ c ∨ ¬ f)) ∧ (¬ d ∨ ¬ g)) ∧ (¬ d ∨ ¬ h)) ∧ (a ∨ b)) ∧ (c ∨ d)) ∧ ((¬ b ∨ e) ∨ f)) ∧ ((¬ b ∨ g) ∨ h))
                  atp-strip $  -- Γ ⊢ (((((((((¬ a ∧ (a ∨ b)) ∧ (c ∨ d)) ∧ ((¬ b ∨ e) ∨ f)) ∧ (¬ c ∨ ¬ e)) ∧ (¬ c ∨ ¬ f)) ∧ ((¬ b ∨ g) ∨ h)) ∧ (¬ d ∨ ¬ g)) ∧ (¬ d ∨ ¬ h)) ⇒ ⊥)
                    assume {Γ = Γ} $  -- Γ ⊢ ¬ (((((((((¬ a ∧ (a ∨ b)) ∧ (c ∨ d)) ∧ ((¬ b ∨ e) ∨ f)) ∧ (¬ c ∨ ¬ e)) ∧ (¬ c ∨ ¬ f)) ∧ ((¬ b ∨ g) ∨ h)) ∧ (¬ d ∨ ¬ g)) ∧ (¬ d ∨ ¬ h)) ⇒ ⊥)
                      atp-neg subgoal₁₄
          )
      )

proof : Γ ⊢ goal
proof =
  ⇒-elim
    atp-splitGoal
    proof₀

