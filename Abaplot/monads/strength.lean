import Std 

/-
  Monad strength
  defines simply the strength of a monad and the notation used
-/

def strength (X Y : Type) (M : Type → Type) [Monad M] := X × M Y → M (X × Y)

class StrongMonad (M : Type → Type) extends Monad M where
  strong : strength X Y M