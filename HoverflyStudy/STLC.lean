import Hoverfly.Backend
import Aesop

namespace STLC

/-
Here we define a small programming language, the simply-typed lambda calculus,
which contains variables, functions, if/then/else branching, and booleans.
-/

/-
All terms are either booleans or have a function type (arrow T₁ T₂ for some
types T₁ T₂).
-/
inductive Ty where
  | bool : Ty
  | arrow : Ty → Ty → Ty
  deriving DecidableEq, Repr

/-
Terms can be variables, functions, true or false, if/then/else branching, or
function applications.
-/
inductive Tm where
  | var : String → Tm
  | lam : String → Ty → Tm → Tm
  | tru : Tm
  | fls : Tm
  | ite : Tm → Tm → Tm → Tm
  | app : Tm → Tm → Tm
  deriving DecidableEq, Repr

/-
Values are either functions, true, or false. Conceptually, we think of these
as the terms that are "terminal", i.e., they do not step to anything. However,
that is not part of the definition.
-/
inductive Value : Tm → Prop where
  | lam : Value (.lam x T body)
  | tru : Value .tru
  | fls : Value .fls

/-
subst defines how to substitute a variable throughout a term. I.e., in
the term (.app x y), we might substitute fls in for x to get (.app fls y).
-/
def subst (x : String) (s : Tm) : Tm → Tm
  | .var y => if x = y then s else .var y
  | .lam y T body => if x = y then .lam y T body else .lam y T (subst x s body)
  | .tru => .tru
  | .fls => .fls
  | .ite c t e => .ite (subst x s c) (subst x s t) (subst x s e)
  | .app t₁ t₂ => .app (subst x s t₁) (subst x s t₂)

/-
This defines the various ways a term can step. We can apply a function, choose
a branch within an if/then/else construction based on the condition, or
simplify (step) a subterm within a function application or an if/then/else.
-/
inductive Step : Tm → Tm → Prop where
  | appAbs : Value v → Step (.app (.lam x T body) v) (subst x v body)
  | iteTru : Step (.ite .tru t e) t
  | iteFls : Step (.ite .fls t e) e
  | ite : Step c c' → Step (.ite c t e) (.ite c' t e)
  | app₁ : Step t₁ t₁' → Step (.app t₁ t₂) (.app t₁' t₂)
  | app₂ : Value v₁ → Step t₂ t₂' → Step (.app v₁ t₂) (.app v₁ t₂')

infix:40 " ==> " => Step

/-
MultiStep corresponds 0 or more steps. That is, MultiStep t₁ t₂ means there is
a path from t₁ to t₂.
-/
inductive MultiStep : Tm → Tm → Prop where
  | refl : MultiStep t t
  | head : Step t₁ t₂ → MultiStep t₂ t₃ → MultiStep t₁ t₃

infix:40 " ==>* " => MultiStep

/-
The context of a program gives the types corresponding to variables. As
defined, it does not guarantee that all variables in the program are
listed in the context, that all variables in the context appear in the
program, or that variables appear only once in the list.
-/
abbrev Ctx := List (String × Ty)

/-
We can look up variables in a context. If a variable appears multiple
times in the context, we will default to its first appearance. -/
def Ctx.lookup : Ctx → String → Option Ty
  | [], _ => none
  | (y, T) :: Γ, x => if x = y then some T else Ctx.lookup Γ x

/- We will never find values for variables in the empty context. -/
@[simp] theorem Ctx.lookup_nil (x : String) : Ctx.lookup [] x = none := rfl

/-
In a nonempty context, either the variable we are looking for is the first
in the list and its type is the first type, or the result of the lookup is
the same as the result of looking it up in the rest of the list. -/
@[simp] theorem Ctx.lookup_cons (Γ : Ctx) (x y : String) (T : Ty) :
    Ctx.lookup ((y, T) :: Γ) x = if x = y then some T else Ctx.lookup Γ x := rfl

/- HasType Γ t T means that in context Γ, term t has type T. -/
inductive HasType : Ctx → Tm → Ty → Prop where
  | var : Γ.lookup x = some T → HasType Γ (.var x) T
  | lam : HasType ((x, T₁) :: Γ) body T₂ → HasType Γ (.lam x T₁ body) (.arrow T₁ T₂)
  | tru : HasType Γ .tru .bool
  | fls : HasType Γ .fls .bool
  | ite : HasType Γ c .bool → HasType Γ t T → HasType Γ e T → HasType Γ (.ite c t e) T
  | app : HasType Γ t₁ (.arrow T₁ T₂) → HasType Γ t₂ T₁ → HasType Γ (.app t₁ t₂) T₂

notation:40 Γ " ⊢ " t " ∶ " T => HasType Γ t T

/- A term is _stuck_ if it cannot step but is not a value. -/
def Stuck (t : Tm) : Prop := (¬ ∃ t', t ==> t') ∧ ¬ Value t

/-
Here we add tactics and our definitions to Hoverfly.
We can add arbitrary tactics here and, if we wanted, could add
all tactics available to Aesop to Hoverfly with one command.
Tactics of the form "<tactic> HYP" will be replaced by "<tactic> x"
for various x from the context. For tactics with more arguments, we
would add HYP the corresponding number of times.
-/
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
  revert HYP
  cases HYP
  induction HYP
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


/-! ## Preservation -/

/- --------------------------- Problem A --------------------------- -/

/-
If Γ is a "subcontext" of Δ (i.e., all variables that we can
successfully look up in Γ can be successfully looked up with the same
result in Δ), and t has type T in Γ, then t also has type T in Δ.
-/
theorem weakening (Γ Δ : Ctx) (t : Tm) (T : Ty)
    (hsub : ∀ x U, Γ.lookup x = some U → Δ.lookup x = some U)
    (ht : Γ ⊢ t ∶ T) :
    Δ ⊢ t ∶ T := by
  sorry

add_hoverfly_tactics [
  apply weakening
]

/-
Corollary: if t has type T in the empty context, then it has type T
in any context.
-/
theorem weakening_empty (Γ : Ctx) (t : Tm) (T : Ty) (ht : [] ⊢ t ∶ T) :
    Γ ⊢ t ∶ T := by
  sorry

add_hoverfly_tactics [
  apply weakening_empty
]

/- ------------------------- End Problem A ------------------------- -/

/-
Leftmost appearances in a context "shadow" other appearances. That is,
if x appears twice* in a context, that is the same as if it
only appeared the first time.

*Technically this is "twice in a row" here, but that will become
irrelevant with lookup_swap.
-/
theorem lookup_shadow (Γ : Ctx) (x : String) (T U : Ty) :
    ∀ y W, Ctx.lookup ((x, T) :: (x, U) :: Γ) y = some W →
           Ctx.lookup ((x, T) :: Γ) y = some W := by
  aesop

/-
We can swap the order of different elements of the context as long as the
variables are different.
-/
theorem lookup_swap (Γ : Ctx) (x y : String) (T U : Ty) (hxy : x ≠ y) :
    ∀ z W, Ctx.lookup ((y, T) :: (x, U) :: Γ) z = some W →
           Ctx.lookup ((x, U) :: (y, T) :: Γ) z = some W := by
  aesop

add_hoverfly_tactics [
  apply lookup_shadow
  apply lookup_swap
]

/-
If t has type T in context Γ where x appears with type U, and v has type U in
the empty context, then we can substitute v in for x in t without changing
t's type.
-/
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
  | app t₁ t₂ ih₁ ih₂ =>
    cases ht with
    | app ht₁ ht₂ =>
      simp only [subst]
      exact .app (ih₁ _ _ ht₁) (ih₂ _ _ ht₂)

add_hoverfly_tactics [
  apply substitution_preserves_typing
]

/-
If t has type T in the empty context, and t steps (in one step) to t', then t' must
also have type T in the empty context.
-/
theorem preservation (t t' : Tm) (T : Ty) (ht : [] ⊢ t ∶ T) (hstep : t ==> t') :
    [] ⊢ t' ∶ T := by
  induction hstep generalizing T with
  | appAbs hv =>
    cases ht with
    | app ht₁ ht₂ =>
      cases ht₁ with
      | lam hbody => exact substitution_preserves_typing _ _ _ _ _ _ hbody ht₂
  | iteTru =>
    cases ht with
    | ite _ hth _ => exact hth
  | iteFls =>
    cases ht with
    | ite _ _ hel => exact hel
  | ite _ ih =>
    cases ht with
    | ite hc hth hel => exact .ite (ih _ hc) hth hel
  | app₁ _ ih =>
    cases ht with
    | app ht₁ ht₂ => exact .app (ih _ ht₁) ht₂
  | app₂ _ _ ih =>
    cases ht with
    | app ht₁ ht₂ => exact .app ht₁ (ih _ ht₂)

add_hoverfly_tactics [
  apply preservation
]

/-! ## Consequences -/

/- --------------------------- Problem B --------------------------- -/

/-
Preservation, but with potentially multiple steps.

If t has type T in the empty context, and t steps (in zero or more steps) to
t', then t' must also have type T in the empty context.
-/
theorem preservation_multi (t t' : Tm) (T : Ty)
    (ht : [] ⊢ t ∶ T) (hsteps : t ==>* t') :
    [] ⊢ t' ∶ T := by
  sorry

/-
Canonical forms for booleans.
If a value has type bool int he empty context, it is either true or false.
-/
theorem canonical_forms_bool (t : Tm) (ht : [] ⊢ t ∶ .bool) (hv : Value t) :
    t = .tru ∨ t = .fls := by
  sorry

/- ------------------------- End Problem B ------------------------- -/
