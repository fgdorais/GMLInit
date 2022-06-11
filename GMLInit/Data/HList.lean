import GMLInit.Data.Basic
import GMLInit.Data.HVal
import GMLInit.Logic.ListConnectives
import GMLInit.Meta.Basic
import GMLInit.Meta.Relation

inductive HList.{u} : List (Sort u) → Type u
| nil : HList []
| cons {α αs} : α → HList αs → HList (α :: αs)

namespace HList

scoped infixr:67 " :: " => HList.cons
scoped syntax (name := hlist) "[" term,* "]"  : term
scoped macro_rules (kind := hlist)
  | `([ ])           => `(HList.nil)
  | `([ $a ])        => `(HList.cons $a HList.nil)
  | `([ $a, $as,* ]) => `(HList.cons $a [$as,*])

protected def extAux : {αs βs : List (Sort _)} → (as : HList αs) → (bs : HList βs) → List Prop
| [], [], [], [] => []
| [], _::_, [], _::_ => [False]
| _::_, [],  _::_, [] => [False]
| _::_, _::_, a::as, b::bs => (a ≅ b) :: HList.extAux as bs

protected theorem ext {αs : List (Sort _)} (as₁ as₂ : HList αs) : All (HList.extAux as₁ as₂) → as₁ = as₂ := by
  intro h
  induction as₁ with
  | nil =>
    cases as₂ with
    | nil => rfl
  | cons a₁ as₁ H =>
    cases as₂ with
    | cons a₂ as₂ =>
      cases h with
      | cons h hs =>
        rw [eq_of_heq h, H _ hs]

protected theorem dext {αs βs : List (Sort _)} (as : HList αs) (bs : HList βs) : αs = βs → All (HList.extAux as bs) → as ≅ bs := by
  intro ht hs
  cases ht
  apply heq_of_eq
  apply HList.ext
  exact hs

protected def mk : {αs : List (Sort _)} → ((i : Index αs) → i.val) → HList αs
| [], _ => []
| _::_, v => v .head :: HList.mk λ i => v (.tail i)

protected def ofList {α} : (as : List α) → HList (as.map λ _ => α)
| [] => []
| a::as => a :: HList.ofList as

protected def ofListHVal : (vs : List HVal) → HList (vs.map HVal.sort)
| [] => []
| v::vs => v.val :: HList.ofListHVal vs

def append : {αs βs : List (Sort _)} → HList αs → HList βs → HList (αs ++ βs)
| [], _, [], bs => bs
| α :: αs, βs, a::as, bs => List.cons_append α αs βs ▸ cons a (append as bs)

def eval : {αs : List (Sort _)} → HList αs → (i : Index αs) → i.val
| _::_, a::_, .head => a
| _::_, _::as, .tail i => eval as i

def equiv (αs : List (Sort _)) : Equiv (HList αs) ((i : Index αs) → i.val) where
  fwd := HList.eval
  rev := HList.mk
  spec := by
    intros as f
    constr
    · intro h
      cases h
      induction as with
      | nil => rfl
      | cons a as H => unfold HList.mk HList.eval; rw [H]
    · intro h
      cases h
      funext i
      induction i with
      | head => rfl
      | tail i H => unfold HList.eval HList.mk; rw [H]

end HList
