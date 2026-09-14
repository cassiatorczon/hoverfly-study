import Hoverfly.Backend
import Aesop

namespace STLC

inductive Ty where
  | bool : Ty
  | arrow : Ty → Ty → Ty
  deriving DecidableEq, Repr

inductive Tm where
  | var : String → Tm
  | app : Tm → Tm → Tm
  | lam : String → Ty → Tm → Tm
  | tru : Tm
  | fls : Tm
  | ite : Tm → Tm → Tm → Tm
  deriving DecidableEq, Repr

inductive Value : Tm → Prop where
  | lam : Value (.lam x T body)
  | tru : Value .tru
  | fls : Value .fls

def subst (x : String) (s : Tm) : Tm → Tm
  | .var y => if x = y then s else .var y
  | .app t₁ t₂ => .app (subst x s t₁) (subst x s t₂)
  | .lam y T body => if x = y then .lam y T body else .lam y T (subst x s body)
  | .tru => .tru
  | .fls => .fls
  | .ite c t e => .ite (subst x s c) (subst x s t) (subst x s e)

inductive Step : Tm → Tm → Prop where
  | appAbs : Value v → Step (.app (.lam x T body) v) (subst x v body)
  | app₁ : Step t₁ t₁' → Step (.app t₁ t₂) (.app t₁' t₂)
  | app₂ : Value v₁ → Step t₂ t₂' → Step (.app v₁ t₂) (.app v₁ t₂')
  | iteTru : Step (.ite .tru t e) t
  | iteFls : Step (.ite .fls t e) e
  | ite : Step c c' → Step (.ite c t e) (.ite c' t e)

infix:40 " ==> " => Step

inductive MultiStep : Tm → Tm → Prop where
  | refl : MultiStep t t
  | head : Step t₁ t₂ → MultiStep t₂ t₃ → MultiStep t₁ t₃

infix:40 " ==>* " => MultiStep

abbrev Ctx := List (String × Ty)

def Ctx.lookup : Ctx → String → Option Ty
  | [], _ => none
  | (y, T) :: Γ, x => if x = y then some T else Ctx.lookup Γ x

@[simp] theorem Ctx.lookup_nil (x : String) : Ctx.lookup [] x = none := rfl

@[simp] theorem Ctx.lookup_cons (Γ : Ctx) (x y : String) (T : Ty) :
    Ctx.lookup ((y, T) :: Γ) x = if x = y then some T else Ctx.lookup Γ x := rfl

inductive HasType : Ctx → Tm → Ty → Prop where
  | var : Γ.lookup x = some T → HasType Γ (.var x) T
  | lam : HasType ((x, T₁) :: Γ) body T₂ → HasType Γ (.lam x T₁ body) (.arrow T₁ T₂)
  | app : HasType Γ t₁ (.arrow T₁ T₂) → HasType Γ t₂ T₁ → HasType Γ (.app t₁ t₂) T₂
  | tru : HasType Γ .tru .bool
  | fls : HasType Γ .fls .bool
  | ite : HasType Γ c .bool → HasType Γ t T → HasType Γ e T → HasType Γ (.ite c t e) T

notation:40 Γ " ⊢ " t " ∶ " T => HasType Γ t T

def Stuck (t : Tm) : Prop := (¬ ∃ t', t ==> t') ∧ ¬ Value t

add_hoverfly_tactics [
  intros
  assumption
  apply_assumption
  rfl
  contradiction
  subst_eqs
  split
  constructor
  left
  right
  simp
  simp_all
  aesop
  grind
]

add_hoverfly_tactics [
  simp_all [subst]
  simp_all [Ctx.lookup]
  simp_all [Stuck]
  simp_all [subst, Ctx.lookup]
]

add_hoverfly_tactics [
  apply HasType.var
  apply HasType.lam
  apply HasType.app
  apply HasType.tru
  apply HasType.fls
  apply HasType.ite
]

add_hoverfly_tactics [
  apply Value.lam
  apply Value.tru
  apply Value.fls
  apply Step.appAbs
  apply Step.app₁
  apply Step.app₂
  apply Step.iteTru
  apply Step.iteFls
  apply Step.ite
  apply MultiStep.refl
  apply MultiStep.head
]

/-! ## Canonical forms -/

/- Theorem 1 -/
theorem canonical_forms_bool (t : Tm) (ht : [] ⊢ t ∶ .bool) (hv : Value t) :
    t = .tru ∨ t = .fls := by
  -- ✅ Good for hoverfly
  hoverfly

/- Theorem 2 -/
theorem canonical_forms_fun (t : Tm) (T₁ T₂ : Ty)
    (ht : [] ⊢ t ∶ .arrow T₁ T₂) (hv : Value t) :
    ∃ x body, t = .lam x T₁ body := by
  -- ✅ Good for hoverfly
  hoverfly

add_hoverfly_tactics [
  apply canonical_forms_bool
  apply canonical_forms_fun
]

/-! ## Progress -/

/- Theorem 3 -/
theorem progress (t : Tm) (T : Ty) (ht : [] ⊢ t ∶ T) :
    Value t ∨ ∃ t', t ==> t' := by
  -- ❌ Hard for hoverfly
  --
  -- You need to be careful about how you specialize your IHs in the `app` case, and
  -- `apply_assumption` doesn't do what you want
  hoverfly

add_hoverfly_tactics [
  apply progress
]

/-! ## Preservation -/

/- Theorem 4 -/
theorem weakening (Γ Δ : Ctx) (t : Tm) (T : Ty)
    (hsub : ∀ x U, Γ.lookup x = some U → Δ.lookup x = some U)
    (ht : Γ ⊢ t ∶ T) :
    Δ ⊢ t ∶ T := by
  -- ✅ Good for hoverfly
  hoverfly

add_hoverfly_tactics [
  apply weakening
]

/- Theorem 5 -/
theorem weakening_empty (Γ : Ctx) (t : Tm) (T : Ty) (ht : [] ⊢ t ∶ T) :
    Γ ⊢ t ∶ T := by
  -- ✅ Good for hoverfly
  -- This has an nteresting instance where order of mvars matters
  hoverfly

add_hoverfly_tactics [
  apply weakening_empty
]

theorem lookup_shadow (Γ : Ctx) (x : String) (T U : Ty) :
    ∀ y W, Ctx.lookup ((x, T) :: (x, U) :: Γ) y = some W →
           Ctx.lookup ((x, T) :: Γ) y = some W := by
  aesop

theorem lookup_swap (Γ : Ctx) (x y : String) (T U : Ty) (hxy : x ≠ y) :
    ∀ z W, Ctx.lookup ((y, T) :: (x, U) :: Γ) z = some W →
           Ctx.lookup ((x, U) :: (y, T) :: Γ) z = some W := by
  aesop

add_hoverfly_tactics [
  apply lookup_shadow
  apply lookup_swap
]

/- Theorem 6 -/
theorem substitution_preserves_typing (Γ : Ctx) (x : String) (U T : Ty) (t v : Tm)
    (ht : ((x, U) :: Γ) ⊢ t ∶ T) (hv : [] ⊢ v ∶ U) :
    Γ ⊢ subst x v t ∶ T := by
  -- TODO: I haven't gotten to this yet, but it's pretty involved so I suspect it's not going to be
  -- obvious
  hoverfly

add_hoverfly_tactics [
  apply substitution_preserves_typing
]

/- Theorem 7 -/
theorem preservation (t t' : Tm) (T : Ty) (ht : [] ⊢ t ∶ T) (hstep : t ==> t') :
    [] ⊢ t' ∶ T := by
  -- ⚠️ Mostly good for hoverfly
  -- This keeps triggering a bug where I close all
  -- of the cases but for some reason the final proof still has a sorry. I suspect some goal is
  -- getting dropped? But I'm not sure
  hoverfly

add_hoverfly_tactics [
  apply preservation
]

/-! ## Consequences -/

/- Theorem 8 -/
theorem preservation_multi (t t' : Tm) (T : Ty)
    (ht : [] ⊢ t ∶ T) (hsteps : t ==>* t') :
    [] ⊢ t' ∶ T := by
  -- ✅ Good for hoverfly
  -- There are some wrong turns here that backtracking helps with
  hoverfly

/- Theorem 9 -/
theorem soundness (t t' : Tm) (T : Ty) (ht : [] ⊢ t ∶ T) (hsteps : t ==>* t') :
    ¬ Stuck t' := by
  -- ❌ Hard for hoverfly
  -- Hoverfly can actually do the proof from here, but you need to instantiate progress and
  -- preservation first
  have ht' := preservation_multi _ _ _ ht hsteps
  have := progress _ _ ht'
  hoverfly

end STLC
