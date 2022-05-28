import GMLInit.Prelude

deriving instance DecidableEq for Ordering

structure Equiv.{u,v} (α : Sort u) (β : Sort v) : Sort (max 1 (max u v)) where
  fwd : α → β
  rev : β → α
  spec {x y} : fwd x = y ↔ rev y = x

inductive Index.{u} {α : Type u} : List α → Type u where
| head {a : α} {as : List α} : Index (a :: as)
| tail {a : α} {as : List α} : Index as → Index (a :: as)
deriving Repr

instance Index.instDecidableEq {α} : {xs : List α} → DecidableEq (Index xs)
| _::_, head, head => isTrue rfl
| _::_, head, tail _ => isFalse Index.noConfusion
| _::_, tail _, head => isFalse Index.noConfusion
| _::_, tail i, tail j =>
  match instDecidableEq i j with
  | isTrue rfl => isTrue rfl
  | isFalse h => isFalse fun | rfl => h rfl

@[reducible] def Index.val {α} : {as : List α} → Index as → α
| a::_, head => a
| _::_, tail i => val i
