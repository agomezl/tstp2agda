
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

