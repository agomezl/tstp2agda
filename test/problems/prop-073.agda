
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

-- Axiom
a₁ : Prop
a₁ = ((p ∧ q) ∨ (p ∧ r))


-- Premise
Γ : Ctxt
Γ = [ a1 ]

-- Conjecture
goal : Prop
goal = (p ∧ (q ∨ r))


-- Subgoals
subgoal₀ : Prop
subgoal₀ = p


subgoal₁ : Prop
subgoal₁ = ((p ∧ ¬ q) ⇒ r)

-- Metis Proof.
proof₀ : Γ ⊢ subgoal₀
proof₀ =
  RAA $
    atp-canonicalize $  -- Γ ⊢ ({ p : Set} → ¬ p)
      atp-canonicalize $  -- Γ ⊢ ¬ p
        atp-strip $  -- Γ ⊢ p
          assume {Γ = Γ} $  -- Γ ⊢ ¬ p
            atp-neg subgoal₀

proof₁ : Γ ⊢ subgoal₁
proof₁ =
  RAA $
    atp-canonicalize $  -- Γ ⊢ ({ p : Set} → p)
      ∧-proj₁ $ -- 1: ((p ∧ (p ∨ q)) ∧ (p ∨ r))
        ? -- inference rule no supported yet $  -- Γ ⊢ (((p ∧ (p ∨ q)) ∧ (p ∨ r)) ∧ (q ∨ r))
          atp-canonicalize $  -- Γ ⊢ ((p ∧ q) ∨ (p ∧ r))
            weaken (atp-neg subgoal₁) $
              (assume {Γ = ∅} a1)

proof₂ : Γ ⊢ subgoal₂
proof₂ =
  RAA $
    id -- resolve 4.
      (
              atp-canonicalize $  -- Γ ⊢ ({ p : Set} → p)
          ∧-proj₁ $ -- 1: ((p ∧ (p ∨ q)) ∧ (p ∨ r))
            ? -- inference rule no supported yet $  -- Γ ⊢ (((p ∧ (p ∨ q)) ∧ (p ∨ r)) ∧ (q ∨ r))
              atp-canonicalize $  -- Γ ⊢ ((p ∧ q) ∨ (p ∧ r))
                weaken (atp-neg subgoal₂) $
                  (assume {Γ = ∅} a1)
      )
      (
              atp-canonicalize $  -- Γ ⊢ ({ p : Set} → ¬ p)
          atp-canonicalize $  -- Γ ⊢ ¬ p
            atp-strip $  -- Γ ⊢ p
              assume {Γ = Γ} $  -- Γ ⊢ ¬ p
                atp-neg subgoal₂
      )

proof₃ : Γ ⊢ subgoal₃
proof₃ =
  RAA $
    atp-canonicalize $  -- Γ ⊢ ({ q r : Set} → q ∨ r)
      ∧-proj₂ $ -- ((q ∨ r) ≟ (q ∨ r))
        ? -- inference rule no supported yet $  -- Γ ⊢ (((p ∧ (p ∨ q)) ∧ (p ∨ r)) ∧ (q ∨ r))
          atp-canonicalize $  -- Γ ⊢ ((p ∧ q) ∨ (p ∧ r))
            weaken (atp-neg subgoal₃) $
              (assume {Γ = ∅} a1)

proof₄ : Γ ⊢ subgoal₄
proof₄ =
  RAA $
    atp-canonicalize $  -- Γ ⊢ ({ q : Set} → ¬ q)
      ∧-proj₁ $ -- 1: (¬ q ∧ ¬ r)
        atp-canonicalize $  -- Γ ⊢ ((¬ q ∧ ¬ r) ∧ p)
          atp-strip $  -- Γ ⊢ ((p ∧ ¬ q) ⇒ r)
            assume {Γ = Γ} $  -- Γ ⊢ ¬ ((p ∧ ¬ q) ⇒ r)
              atp-neg subgoal₄

proof₅ : Γ ⊢ subgoal₅
proof₅ =
  RAA $
    id -- resolve 4.
      (
              atp-canonicalize $  -- Γ ⊢ ({ q r : Set} → q ∨ r)
          ∧-proj₂ $ -- ((q ∨ r) ≟ (q ∨ r))
            ? -- inference rule no supported yet $  -- Γ ⊢ (((p ∧ (p ∨ q)) ∧ (p ∨ r)) ∧ (q ∨ r))
              atp-canonicalize $  -- Γ ⊢ ((p ∧ q) ∨ (p ∧ r))
                weaken (atp-neg subgoal₅) $
                  (assume {Γ = ∅} a1)
      )
      (
              atp-canonicalize $  -- Γ ⊢ ({ q : Set} → ¬ q)
          ∧-proj₁ $ -- 1: (¬ q ∧ ¬ r)
            atp-canonicalize $  -- Γ ⊢ ((¬ q ∧ ¬ r) ∧ p)
              atp-strip $  -- Γ ⊢ ((p ∧ ¬ q) ⇒ r)
                assume {Γ = Γ} $  -- Γ ⊢ ¬ ((p ∧ ¬ q) ⇒ r)
                  atp-neg subgoal₅
      )

proof₆ : Γ ⊢ subgoal₆
proof₆ =
  RAA $
    atp-canonicalize $  -- Γ ⊢ ({ r : Set} → ¬ r)
      ∧-proj₁ $ -- 1: (¬ q ∧ ¬ r)
        atp-canonicalize $  -- Γ ⊢ ((¬ q ∧ ¬ r) ∧ p)
          atp-strip $  -- Γ ⊢ ((p ∧ ¬ q) ⇒ r)
            assume {Γ = Γ} $  -- Γ ⊢ ¬ ((p ∧ ¬ q) ⇒ r)
              atp-neg subgoal₆

proof₇ : Γ ⊢ subgoal₇
proof₇ =
  RAA $
    id -- resolve 4.
      (
              id -- resolve 4.
          (
                      atp-canonicalize $  -- Γ ⊢ ({ q r : Set} → q ∨ r)
              ∧-proj₂ $ -- ((q ∨ r) ≟ (q ∨ r))
                ? -- inference rule no supported yet $  -- Γ ⊢ (((p ∧ (p ∨ q)) ∧ (p ∨ r)) ∧ (q ∨ r))
                  atp-canonicalize $  -- Γ ⊢ ((p ∧ q) ∨ (p ∧ r))
                    weaken (atp-neg subgoal₇) $
                      (assume {Γ = ∅} a1)
          )
          (
                      atp-canonicalize $  -- Γ ⊢ ({ q : Set} → ¬ q)
              ∧-proj₁ $ -- 1: (¬ q ∧ ¬ r)
                atp-canonicalize $  -- Γ ⊢ ((¬ q ∧ ¬ r) ∧ p)
                  atp-strip $  -- Γ ⊢ ((p ∧ ¬ q) ⇒ r)
                    assume {Γ = Γ} $  -- Γ ⊢ ¬ ((p ∧ ¬ q) ⇒ r)
                      atp-neg subgoal₇
          )
      )
      (
              atp-canonicalize $  -- Γ ⊢ ({ r : Set} → ¬ r)
          ∧-proj₁ $ -- 1: (¬ q ∧ ¬ r)
            atp-canonicalize $  -- Γ ⊢ ((¬ q ∧ ¬ r) ∧ p)
              atp-strip $  -- Γ ⊢ ((p ∧ ¬ q) ⇒ r)
                assume {Γ = Γ} $  -- Γ ⊢ ¬ ((p ∧ ¬ q) ⇒ r)
                  atp-neg subgoal₇
      )

proof : Γ ⊢ goal
proof =
  ⇒-elim
    atp-splitGoal
    (
    ∧-intro
      subgoal₀
      subgoal₁
    )

