import Mathlib.Algebra.Group.Defs
import Mathlib.Data.Nat.Basic
import Abaplot.monads.selection_aug

-- The writer monad is rather easy to implement.
-- It is also strong with a simple strength operation.

def writer [CommMonoid R] (X : Type) := R × X

example : writer (R := Nat) Nat := ⟨1,2⟩

def writer_unit [CommMonoid R] : X → writer (R := R) X := λ x => ⟨One.one , x⟩
def writer_bind [CommMonoid R] : (X → writer (R := R) Y) → writer (R := R) X → writer (R := R) Y := 
λ f x => let ⟨r , y⟩ := f x.2 ; ⟨Mul.mul x.1 r , y⟩    


instance [CommMonoid R] : Monad (writer (R := R)) where
 pure := writer_unit
 bind x f := writer_bind f x

instance [CommMonoid R] : StrongMonad (writer (R := R)) where
  strong := λ (x, (r, y)) =>  (r, (x,y))

instance [CommMonoid R] : Algebra (writer (R := R)) R where
  obj := 1
  morph := λ (r,s) => r * s

-- selection monad augmented with writer
def select_aug_with_writer [CommMonoid R] := select_aug (T := writer (R:= R)) (R := R) 

