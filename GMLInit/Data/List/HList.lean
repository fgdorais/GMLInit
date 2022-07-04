import GMLInit.Data.Basic
import GMLInit.Data.HVal
import GMLInit.Data.List.Basic
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

protected theorem cons_hcongr {α β} {αs βs : List (Sort _)} {a : α} {b : β} {as : HList αs} {bs : HList βs} : α = β → αs = βs → a ≅ b → as ≅ bs → HList.cons a as ≅ HList.cons b bs
| rfl, rfl, HEq.rfl, HEq.rfl => HEq.rfl

protected def ofList {α} : (as : List α) → HList (as.map λ _ => α)
| [] => []
| a::as => a :: HList.ofList as

protected def ofListHVal : (vs : List HVal) → HList (vs.map HVal.sort)
| [] => []
| v::vs => v.val :: HList.ofListHVal vs

protected def append : {αs βs : List (Sort _)} → HList αs → HList βs → HList (αs ++ βs)
| [], _, [], bs => bs
| α :: αs, βs, a::as, bs => List.cons_append α αs βs ▸ cons a (HList.append as bs)

protected theorem nil_append {βs : List (Sort _)} (bs : HList βs) : HList.append [] bs = bs := rfl

protected theorem cons_append {α : Sort _} {αs βs : List (Sort _)} (a : α) (as : HList αs) (bs : HList βs) : HList.append (a :: as) bs = a :: HList.append as bs := rfl

protected theorem append_nil {αs : List (Sort _)} (as : HList αs) : HList.append as [] ≅ as := by
  induction as with
  | nil => 
    rw [HList.nil_append]
    reflexivity using (.≅.)
  | cons _ _ ih => 
    rw [HList.cons_append]
    apply HList.cons_hcongr
    · reflexivity
    · rw [List.append_nil]
    · reflexivity using (.≅.)
    · exact ih

protected theorem append_assoc {αs βs γs : List (Sort _)} (as : HList αs) (bs : HList βs) (cs : HList γs) : HList.append (HList.append as bs) cs ≅ HList.append as (HList.append bs cs) := by
  induction as with
  | nil => 
    repeat rw [HList.nil_append]
    reflexivity using (.≅.)
  | cons _ _ ih => 
    repeat rw [HList.cons_append]
    apply HList.cons_hcongr
    · reflexivity
    · rw [List.append_assoc]
    · reflexivity using (.≅.)
    · exact ih

protected def mk : {αs : List (Sort _)} → ((i : Index αs) → i.val) → HList αs
| [], _ => []
| _::_, v => v .head :: HList.mk λ i => v (.tail i)

protected def eval : {αs : List (Sort _)} → HList αs → (i : Index αs) → i.val
| _::_, a::_, .head => a
| _::_, _::as, .tail i => HList.eval as i

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
