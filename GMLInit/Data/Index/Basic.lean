import GMLInit.Data.Basic
import GMLInit.Data.Ord
import GMLInit.Meta.Basic
import GMLInit.Meta.Decidable

namespace List.Index

theorem val_ndrec {xs ys : List α} (i : Index xs) : (h : xs = ys) → val (h ▸ i : Index ys) = i.val | rfl => rfl

instance instLinearOrd : (xs : List α) → LinearOrd (Index xs)
| [] => {
  symm := (nomatch .)
  le_trans := (nomatch .)
  eq_strict := (nomatch .)
}
| _::xs => {
  symm := fun
  | head, head => rfl
  | head, tail _ => rfl
  | tail _, head => rfl
  | tail i, tail j => (instLinearOrd xs).symm i j
  le_trans := fun {i j k} hij hjk => match i, j, k, hij, hjk with
  | head, _, head, _, _ => Ordering.noConfusion
  | head, _, tail _, _, _ => Ordering.noConfusion
  | tail _, head, tail _, h, _ => absurd rfl h
  | tail _, tail _, tail _, hij, hjk => (instLinearOrd xs).le_trans hij hjk
  eq_strict := fun {i j} h => match i, j, h with
  | head, head, _ => rfl
  | head, tail _, h => Ordering.noConfusion h
  | tail _, head, h => Ordering.noConfusion h
  | tail _, tail _, h => congrArg tail ((instLinearOrd xs).eq_strict h)
}
