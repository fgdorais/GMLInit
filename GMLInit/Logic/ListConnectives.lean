import GMLInit.Data.Basic
import GMLInit.Logic.Basic
import GMLInit.Meta.Basic

open Meta (termList termOrHole)

inductive All : List Prop → Prop
| protected nil : All []
| protected cons {a as} : a → All as → All (a :: as)

namespace All

@[simp] theorem nil_eq : All [] = True :=
  propext ⟨λ _ => trivial, λ _ => All.nil⟩

@[simp] theorem cons_eq {a as} : All (a :: as) = (a ∧ All as) :=
  propext $ by
  constr
  · intro | All.cons hh ht => exact And.intro hh ht
  · intro | And.intro hh ht => exact All.cons hh ht

protected abbrev head {a as} : All (a :: as) → a
| All.cons h _ => h

protected abbrev tail {a as} : All (a :: as) → All as
| All.cons _ h => h

protected def introIdx : {as : List Prop} → (∀ i : Index as, i.val) → All as
| [], _ => All.nil
| _::_, h => All.cons (h Index.head) (All.introIdx (λ i => h (Index.tail i)))

protected def projIdx : {as : List Prop} → All as → (i : Index as) → i.val
| _::_, All.cons h _, Index.head => h
| _::_, All.cons _ h, Index.tail i => All.projIdx h i

syntax "All.intro" termList : term
macro_rules
| `(All.intro [|$t]) => `($t)
| `(All.intro [$h, $hs,* |$t]) => `(All.cons $h (All.intro [$hs,* |$t]))
| `(All.intro [$hs,*]) => `(All.intro [$hs,*|All.nil])

syntax "All.pr." noWs num termOrHole : term
macro_rules
| `(All.pr.$n $h) => match n.isNatLit? with
  | some 0 => `(All.head $h)
  | some (n+1) =>
    let n := Lean.Syntax.mkNumLit (toString n)
    `(All.pr.$n (All.tail $h))
  | _ => Lean.Macro.throwUnsupported

end All

inductive Any : List Prop → Prop
| protected head {a as} : a → Any (a :: as)
| protected tail {a as} : Any as → Any (a :: as)

namespace Any

@[simp] protected theorem nil_eq : Any [] = False :=
  propext ⟨λ h => nomatch h, False.elim⟩

@[simp] protected theorem cons_eq {a as} : Any (a :: as) = (a ∨ Any as) :=
  propext $ by
  constr
  · intro
    | Any.head h => exact Or.inl h
    | Any.tail h => exact Or.inr h
  · intro
    | Or.inl h => exact Any.head h
    | Or.inr h => exact Any.tail h

protected def elimAll {motive : Prop} : {as : List Prop} → Any as → All (as.map λ a => a → motive) → motive
| _::_, Any.head hh, All.cons h _ => h hh
| _::_, Any.tail ht, All.cons _ h => Any.elimAll ht h

protected def introIdx : {as : List Prop} → (i : Index as) → i.val → Any as
| _::_, Index.head, h => Any.head h
| _::_, Index.tail i, h => Any.tail (Any.introIdx i h)

protected def elimIdx : {as : List Prop} → Any as → (∃ (i : Index as), i.val)
| _::_, Any.head h => ⟨Index.head, h⟩
| _::_, Any.tail h => Exists.elim (Any.elimIdx h) (λ i h => ⟨Index.tail i, h⟩)

syntax "Any.elim" term:max termList : term
macro_rules
| `(Any.elim $h $args:termList) => `(Any.elimAll $h (All.intro $args))

syntax "Any.in." noWs num termOrHole : term
macro_rules
| `(Any.in.$n $h) => match n.isNatLit? with
  | some 0 => `(Any.head $h)
  | some (n+1) => let n := Lean.Syntax.mkNumLit (toString n)
    `(Any.tail (Any.in.$n $h))
  | none => Lean.Macro.throwUnsupported

end Any

theorem all_not_of_not_any : {as : List Prop} → ¬Any as → All (as.map (¬.))
| [], _ => All.nil
| a::as, h => All.cons (λ hh => h (Any.head hh)) $
  all_not_of_not_any λ ht => h (Any.tail ht)

theorem not_any_of_all_not : {as : List Prop} → All (as.map (¬.)) → ¬Any as
| a::as, All.cons na _, Any.head ha => na ha
| a::as, All.cons _ nas, Any.tail has => not_any_of_all_not nas has

theorem not_any_iff_all_not (as : List Prop) : ¬Any as ↔ All (as.map (¬.)) :=
  Iff.intro all_not_of_not_any not_any_of_all_not

theorem Any.deMorgan {as : List Prop} : ¬Any as ↔ All (as.map (¬.)) := not_any_iff_all_not as

theorem not_all_of_any_not : {as : List Prop} → Any (as.map (¬.)) → ¬All as
| a::as, Any.head na, All.cons ha _ => na ha
| a::as, Any.tail nas, All.cons _ has => not_all_of_any_not nas has

theorem any_not_of_not_all : {as : List Prop} → [WeaklyComplementedList as] → ¬All as → Any (as.map (¬.))
| [], _, h => absurd All.nil h
| a::as, WeaklyComplementedList.cons ia ias, h => match ia with
  | WeaklyComplemented.isFalse na => Any.head na
  | WeaklyComplemented.isIrrefutable ha => let nas : ¬All as := λ has => ha λ ha => h (All.cons ha has)
    Any.tail (@any_not_of_not_all as ias nas)

theorem not_all_iff_any_not (as : List Prop) [WeaklyComplementedList as] : ¬All as ↔ Any (as.map (¬.)) :=
  Iff.intro any_not_of_not_all not_all_of_any_not

theorem All.deMorgan {as : List Prop} [WeaklyComplementedList as] : ¬All as ↔ Any (as.map (¬.)) := not_all_iff_any_not as
