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
  cases HYP
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

theorem canonical_forms_bool (t : Tm) (ht : [] ⊢ t ∶ .bool) (hv : Value t) :
    t = .tru ∨ t = .fls := by cases hv
                              · contradiction
                              · aesop
                              · aesop

theorem canonical_forms_fun (t : Tm) (T₁ T₂ : Ty)
    (ht : [] ⊢ t ∶ .arrow T₁ T₂) (hv : Value t) :
    ∃ x body, t = .lam x T₁ body := by
  cases hv
  case lam x T body =>
    exists x, body
    cases ht
    rfl
  case tru => contradiction
  case fls => contradiction

add_hoverfly_tactics [
  apply canonical_forms_bool
  apply canonical_forms_fun
]

/-! ## Progress -/

theorem progress (t : Tm) (T : Ty) (ht : [] ⊢ t ∶ T) :
    Value t ∨ ∃ t', t ==> t' := by
  induction t generalizing T with
  | var y =>
    cases ht with
    | var h => simp at h
  | app t₁ t₂ ih₁ ih₂ =>
    cases ht with
    | app ht₁ ht₂ =>
      right
      rcases ih₁ _ ht₁ with hv₁ | ⟨t₁', hs₁⟩
      · rcases ih₂ _ ht₂ with hv₂ | ⟨t₂', hs₂⟩
        · obtain ⟨x, body, rfl⟩ := canonical_forms_fun _ _ _ ht₁ hv₁
          exact ⟨_, Step.appAbs hv₂⟩
        · exact ⟨_, Step.app₂ hv₁ hs₂⟩
      · exact ⟨_, Step.app₁ hs₁⟩
  | lam x T₁ body _ => exact Or.inl Value.lam
  | tru => exact Or.inl Value.tru
  | fls => exact Or.inl Value.fls
  | ite c th el ihc _ _ =>
    cases ht with
    | ite hc _ _ =>
      right
      rcases ihc _ hc with hv | ⟨c', hs⟩
      · rcases canonical_forms_bool _ hc hv with rfl | rfl
        · exact ⟨_, Step.iteTru⟩
        · exact ⟨_, Step.iteFls⟩
      · exact ⟨_, Step.ite hs⟩

add_hoverfly_tactics [
  apply progress
]


/-! ## Preservation -/

/- Problem A -/
theorem weakening (Γ Δ : Ctx) (t : Tm) (T : Ty)
    (hsub : ∀ x U, Γ.lookup x = some U → Δ.lookup x = some U)
    (ht : Γ ⊢ t ∶ T) :
    Δ ⊢ t ∶ T := by
  hoverfly

add_hoverfly_tactics [
  apply weakening
]

/- Problem A -/
theorem weakening_empty (Γ : Ctx) (t : Tm) (T : Ty) (ht : [] ⊢ t ∶ T) :
    Γ ⊢ t ∶ T := by
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

theorem substitution_preserves_typing (Γ : Ctx) (x : String) (U T : Ty) (t v : Tm)
    (ht : ((x, U) :: Γ) ⊢ t ∶ T) (hv : [] ⊢ v ∶ U) :
    Γ ⊢ subst x v t ∶ T := by
  induction t generalizing Γ T with
  | var y =>
    cases ht with
    | var h =>
      by_cases hxy : x = y
      · subst hxy
        simp at h
        subst h
        simpa [subst] using weakening_empty Γ v _ hv
      · simp only [subst, if_neg hxy]
        simp [Ne.symm hxy] at h
        exact .var h
  | app t₁ t₂ ih₁ ih₂ =>
    cases ht with
    | app ht₁ ht₂ =>
      simp only [subst]
      exact .app (ih₁ _ _ ht₁) (ih₂ _ _ ht₂)
  | lam y T₁ body ih =>
    cases ht with
    | lam hbody =>
      by_cases hxy : x = y
      · subst hxy
        simp only [subst]
        exact .lam (weakening _ _ _ _ (lookup_shadow _ _ _ _) hbody)
      · simp only [subst, if_neg hxy]
        exact .lam (ih _ _ (weakening _ _ _ _ (lookup_swap _ _ _ _ _ hxy) hbody))
  | tru =>
    cases ht with
    | tru => simpa [subst] using HasType.tru
  | fls =>
    cases ht with
    | fls => simpa [subst] using HasType.fls
  | ite c th el ihc iht ihe =>
    cases ht with
    | ite hc hth hel =>
      simp only [subst]
      exact .ite (ihc _ _ hc) (iht _ _ hth) (ihe _ _ hel)

add_hoverfly_tactics [
  apply substitution_preserves_typing
]

theorem preservation (t t' : Tm) (T : Ty) (ht : [] ⊢ t ∶ T) (hstep : t ==> t') :
    [] ⊢ t' ∶ T := by
  induction hstep generalizing T with
  | appAbs hv =>
    cases ht with
    | app ht₁ ht₂ =>
      cases ht₁ with
      | lam hbody => exact substitution_preserves_typing _ _ _ _ _ _ hbody ht₂
  | app₁ _ ih =>
    cases ht with
    | app ht₁ ht₂ => exact .app (ih _ ht₁) ht₂
  | app₂ _ _ ih =>
    cases ht with
    | app ht₁ ht₂ => exact .app ht₁ (ih _ ht₂)
  | iteTru =>
    cases ht with
    | ite _ hth _ => exact hth
  | iteFls =>
    cases ht with
    | ite _ _ hel => exact hel
  | ite _ ih =>
    cases ht with
    | ite hc hth hel => exact .ite (ih _ hc) hth hel

add_hoverfly_tactics [
  apply preservation
]

/-! ## Consequences -/

/- Problem B -/
theorem preservation_multi (t t' : Tm) (T : Ty)
    (ht : [] ⊢ t ∶ T) (hsteps : t ==>* t') :
    [] ⊢ t' ∶ T := by
  hoverfly
