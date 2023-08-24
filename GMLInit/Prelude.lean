import Logic
import Std

instance (α) [Subsingleton α] : DecidableEq α
| _, _ => isTrue (Subsingleton.allEq _ _)

class Inv (α : Type _) where
  inv : α → α
postfix:max "⁻¹" => Inv.inv

class Apart (α : Type _) where
  apart : α → α → Prop
infix:50 " ≶ " => Apart.apart
