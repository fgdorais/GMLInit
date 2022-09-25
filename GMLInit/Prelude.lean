import Lean

instance (α) [Subsingleton α] : DecidableEq α 
| _, _ => isTrue (Subsingleton.allEq _ _)

infix:50 " ≅ " => HEq

class Inv (α : Type _) where
  inv : α → α
postfix:max "⁻¹" => Inv.inv

class Apart (α : Type _) where
  apart : α → α → Prop
infix:50 " ≶ " => Apart.apart
