import GMLInit.Data.List.Basic

structure List1 (α : Type _) where
  protected toList : List α
  ne_nil : toList ≠ []

instance (α : Type _): Coe (List1 α) (List α) where
  coe := List1.toList

protected inductive List1.IndView (α : Type _)
| pure : α → List1.IndView α
| cons : α → List1.IndView α → List1.IndView α

namespace List1
variable {α β : Type _}

protected theorem eq : {xs ys : List1 α} → xs.toList = ys.toList → xs = ys
| ⟨_, _⟩, ⟨_, _⟩, rfl => rfl

protected theorem eta (xs : List1 α) : ⟨xs.toList, xs.ne_nil⟩ = xs := List1.eq rfl

@[match_pattern, inline]
protected def cons (x : α) (xs : List α) : List1 α := ⟨x :: xs, List.noConfusion⟩

@[match_pattern, inline]
protected def pure (x : α) := List1.cons x []

theorem cons_toList (x : α) (xs : List α) : (List1.cons x xs).toList = x :: xs := rfl

theorem sizeOf_toList (xs : List1 α ) : sizeOf xs = 1 + sizeOf xs.toList := rfl

@[simp] theorem sizeOf_cons (x : α) (xs : List α) : sizeOf (List1.cons x xs) = 1 + (1 + sizeOf xs) := rfl

@[inline] def IndView.toList1 : List1.IndView α → List1 α
| pure x => .cons x []
| cons x xs => .cons x (toList1 xs).toList

@[inline] def toIndView : List1 α → List1.IndView α
| .cons x [] => .pure x
| .cons x (x' :: xs') => .cons x (toIndView (.cons x' xs'))

theorem toList1_eq_iff_toIndView_eq {xs : List1.IndView α} {ys : List1 α} :
  xs.toList1 = ys ↔ ys.toIndView = xs := by
  match xs, ys with
  | .pure x, .cons y [] =>
    clean unfold IndView.toList1 toIndView
    constr
    · intro | rfl => rfl
    · intro | rfl => rfl
  | .pure x, .cons y (_ :: _) =>
    clean unfold IndView.toList1 toIndView
    constr
    · intro h; injection h with h; injection h with hh ht; contradiction
    · intro; contradiction
  | .cons x xs, .cons y [] =>
    clean unfold IndView.toList1 toIndView
    constr
    · intro h; injection h with h; injection h with hh ht; absurd ht; exact List1.ne_nil xs.toList1
    · intro; contradiction
  | .cons x xs, .cons y (_ :: _) =>
    clean unfold IndView.toList1 toIndView
    rw [←cons_toList]
    constr
    · intro h; injection h with h; injection h with hh ht
      cases hh
      have ht := List1.eq ht
      congr
      exact toList1_eq_iff_toIndView_eq.mp ht
    · intro h; injection h with hh ht
      cases hh
      congr
      exact toList1_eq_iff_toIndView_eq.mpr ht

@[simp] theorem toIndView_toList1 (xs : List1.IndView α) : xs.toList1.toIndView = xs :=
  toList1_eq_iff_toIndView_eq.mp rfl

@[simp] theorem toList1_toIndView (xs : List1 α) : xs.toIndView.toList1 = xs :=
  toList1_eq_iff_toIndView_eq.mpr rfl

def equivIndView (α : Type _) : Equiv (List1 α) (List1.IndView α) where
  fwd := List1.toIndView
  rev := IndView.toList1
  spec := toList1_eq_iff_toIndView_eq.symm

theorem IndView.sizeOf_toList1 (xs : List1.IndView α) : sizeOf xs.toList1 = 2 + sizeOf xs := by
  induction xs with
  | pure x => rw [toList1]; rfl
  | cons x xs ih => rw [toList1, List1.sizeOf_cons, ←sizeOf_toList, ih, Nat.add_left_comm]; rfl

@[eliminator] def List1.recInd.{u,v} {α : Type v} {motive : List1 α → Sort u}
  (pure : (x : α) → motive (List1.pure x))
  (cons : (x : α) → (xs : List1 α) → motive xs → motive (List1.cons x xs.toList))
  (xs : List1 α) : motive xs :=
  match h : xs.toIndView with
  | .pure x' =>
    have : xs = .pure x' := by
      symmetry
      exact toList1_eq_iff_toIndView_eq.mpr h
    this ▸ pure x'
  | .cons x' xs' =>
    have : xs = .cons x' xs'.toList1.toList := by
      symmetry
      exact toList1_eq_iff_toIndView_eq.mpr h
    this ▸ cons x' xs'.toList1 (List1.recInd pure cons xs'.toList1)
decreasing_by simp_wf; simp_arith [IndView.sizeOf_toList1, this, List1.sizeOf_cons, ←List1.sizeOf_toList]

@[inline] def head : List1 α → α
| .cons x _ => x

@[inline] def tail : List1 α → List α
| .cons _ xs => xs

@[inline] def last : List1 α → α
| .cons x [] => x
| .cons _ (x :: xs) => last (.cons x xs)
decreasing_by simp_wf; simp_arith [List1.sizeOf_cons]

theorem head_cons (x : α) (xs : List α) : (List1.cons x xs).head = x := rfl

theorem tail_cons (x : α) (xs : List α) : (List1.cons x xs).tail = xs := rfl

theorem cons_head_tail : (xs : List1 α) → List1.cons xs.head xs.tail = xs
| .cons _ _ => rfl

def ofList? : List α → Option (List1 α)
| [] => none
| x ::xs => some (.cons x xs)

abbrev append : List1 α → List α → List1 α
| .cons x xs, ys => .cons x (xs ++ ys)

@[scoped simp] theorem append_toList_left (xs : List1 α) (ys : List α) : (xs.append ys).toList = xs.toList ++ ys :=
  match xs with | .cons _ _ => rfl

@[scoped simp] theorem append_toList (xs ys : List1 α) : (xs.append ys).toList = xs.toList ++ ys.toList :=
  append_toList_left xs (ys.toList)

@[scoped simp] theorem append_nil (xs : List1 α) : xs.append [] = xs :=
  match xs with | .cons x xs => congrArg (List1.cons x) (List.append_nil xs)

theorem append_compat_right (xs : List1 α) (ys zs : List α) : (xs.append ys).append zs = xs.append (ys ++ zs) :=
  match xs with | .cons x xs => congrArg (List1.cons x) (List.append_assoc xs ys zs)

theorem append_compat_left (xs ys : List1 α) (zs : List α) : (xs.append ys).append zs = xs.append (ys.append zs) :=
  match xs with | .cons x xs => congrArg (List1.cons x) $ by rw [append_toList_left, List.append_assoc]

theorem append_assoc (xs ys zs : List1 α) : xs.append (ys.append zs) = (xs.append ys).append zs :=
  (append_compat_left xs ys zs.toList).symm

@[inline] def map (f : α → β) : List1 α → List1 β
| ⟨xs, h⟩  => ⟨xs.map f, fun heq => h (List.map_eq_nil.mp heq)⟩

theorem toList_map (f : α → β) (xs : List1 α) : (xs.map f).toList = xs.toList.map f := rfl

@[inline] def bind' (f : α → List1 β) : List1 α → List1 β
| .cons x xs => (f x).append (xs.bind fun x => (f x).toList)

@[inline] def bind : List1 α → (α → List1 β) → List1 β :=
  fun xs f => xs.bind' f

@[inline] def join (xss : List1 (List1 α)) : List1 α := xss.bind id

end List1
