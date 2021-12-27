import GMLInit.Data.Basic
import GMLInit.Data.HVal
import GMLInit.Logic.Eq
import GMLInit.Logic.ListConnectives
import GMLInit.Meta.Basic
import GMLInit.Meta.Relation

inductive HList.{u} : List (Sort u) → Type u
| nil : HList []
| cons {α αs} : α → HList αs → HList (α :: αs)

namespace HList

protected def extAux : {αs βs : List (Sort _)} → (as : HList αs) → (bs : HList βs) → List Prop
| [], [], nil, nil => []
| [], _::_, nil, cons _ _ => [False]
| _::_, [], cons _ _ , nil => [False]
| _::_, _::_, cons a as, cons b bs => (a ≅ b) :: HList.extAux as bs

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
| [], _ => nil
| α::αs, v => cons (v Index.head) (HList.mk λ i => v (Index.tail i))

protected def ofList {α} : (as : List α) → HList (as.map λ _ => α)
| [] => nil
| a::as => cons a (HList.ofList as)

protected def ofListHVal : (vs : List HVal) → HList (vs.map HVal.Sort)
| [] => nil
| v::vs => cons v.val (HList.ofListHVal vs)

def append : {αs βs : List (Sort _)} → HList αs → HList βs → HList (αs ++ βs)
| [], βs, nil, bs => bs
| α :: αs, βs, cons a as, bs => List.cons_append α αs βs ▸ cons a (append as bs)

def eval : {αs : List (Sort _)} → HList αs → (i : Index αs) → i.val
| _::_, cons a _, Index.head => a
| _::_, cons _ as, Index.tail i => eval as i

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
