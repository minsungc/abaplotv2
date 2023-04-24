import Mathlib.Algebra.Group.Defs
import Mathlib.Data.Nat.Basic
import Abaplot.monads.selection_aug
import Mathlib.Init.Algebra.Classes
import Mathlib.Data.Real.Basic
import Mathlib.Data.Fintype.Basic
import Mathlib.Algebra.BigOperators.Basic

/-
We introduce *barycentric* algebras, which are a commutative monoid R equipped with binary probabilistic choice functions [0,1] → R² → R where certain probabilistic inequalities hold.
I'm too lazy to implement the interval [0,1], so we work with general reals.
-/

class BarycentricAlgebra (R : Type) where
  choice_p : Real → R → R → R
  left_unitp x y : choice_p 1 x y = x
  id p x : choice_p p x x = x
  invert p x y : choice_p p x y = choice_p (1 - p) y x
  distr p q x y z : choice_p q (choice_p p x y) z = choice_p (p * q) x (choice_p (((1 - p) * q)/(1 - (p * q))) y z)


class BarycentricCommMonoid (R : Type) extends CommMonoid R, BarycentricAlgebra R where  
  distrib_p p x y z : x * (choice_p p y z) = choice_p p (x*y) (x*z)

class RewardOrder (R : Type) (Ord : R → R → Prop) extends IsTotal R Ord where
  bcm : BarycentricCommMonoid R
  pres_choice_p : ∀ p r s t,  Ord r s ↔ Ord (bcm.choice_p p r t) (bcm.choice_p p s t)
  pres_add : ∀ r s t, Ord r s ↔ Ord (bcm.mul s t) (bcm.mul s t)

class FiniteProbDistr (X : Type) where
  fn : X → ℝ 
  supp : Fintype (Subtype (λ x => fn x ≠ 0))
  sum_to_one : Finset.sum supp.elems (λ x => fn x) = 1

lemma noDup : Multiset.Nodup $ Multiset.ofList [1,2] := by simp
instance : FiniteProbDistr ℕ where
  fn := λ x => if x=1 ∨  x=2 then 1 else 0
  supp := let M := Multiset.ofList [1,2]
          let X := Finset.mk M
          let y :=

