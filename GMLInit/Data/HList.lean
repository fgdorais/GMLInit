import GMLInit.Data.Basic
import GMLInit.Data.HVal
import GMLInit.Meta.Basic

inductive HList.{u} : List (Sort u) → Type u
| nil : HList []
| cons {α αs} : α → HList αs → HList (α :: αs)

namespace HList

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
  spec as vs := by
    split
    · intro h
      cases h
      induction as with
      | nil => rfl
      | cons a as H => simp only [HList.mk, HList.eval, H]; rfl
    · intro h
      cases h
      funext i
      induction i with
      | head => rfl
      | tail i H => simp only [HList.eval, HList.mk, H]; rfl

end HList
