import Std
import Extra
import Logic

class Apart (α : Type _) where
  apart : α → α → Prop
infix:50 " ≶ " => Apart.apart
