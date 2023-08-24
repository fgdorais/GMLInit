import GMLInit.Data.Nat.Basic

namespace Nat
open Logic

def encodeOption : Option Nat → Nat
| some n => n + 1
| none => 0

def decodeOption : Nat → Option Nat
| 0 => none
| n+1 => some n

def equivOption : Equiv (Option Nat) Nat where
  fwd := encodeOption
  rev := decodeOption
  fwd_eq_iff_rev_eq := by
    intro
    | none, y =>
      constructor
      · intro | rfl => rfl
      · intro h
        rw [decodeOption] at h
        split at h
        next => rfl
        next => contradiction
    | some x, y =>
      constructor
      · intro | rfl => rfl
      · intro h
        rw [decodeOption] at h
        split at h
        next => contradiction
        next =>
          rw [encodeOption]
          rw [←h]

end Nat
