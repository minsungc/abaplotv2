import mathport

/-
Some monad implementation. Mostly a warm-up for me implementing abaplot.
Every monad here is outlined in section 2 and 4 of the paper.
-/

-- selection monad 

def select (R X : Type) := (X → R) → X

example : select Nat Nat := λ f => f 0

def cont_rew (f : select R X) (γ : X → R) := γ (f γ)

def select.unit (R : Type) : X → select R X := λ x => (λ _ => x)
def select.bind (R : Type) : (X → select R Y) → select R X → select R Y :=
  λ f => λ F γ => let opt := F (λ x => cont_rew (f x) γ)
                  (f opt) γ 

-- The selection monad needs an instantiated reward type (usually ℤ or ℝ)
instance : Monad (select R) where
 pure := select.unit R
 bind x f := select.bind R f x

-- selection monad augmented with strong aux monad T

def select_aug [Monad T] (R X : Type u) := (X → R) → T X

-- We need that R is a T-algebra, so let's do that.
-- This is read: 
-- the typeclass Algebra takes in T : Type u → Type v, R : Type u,
-- and the fact that T is a monad...

class Algebra (T : Type u  → Type v) (R : Type u ) [Monad T] where
  obj : R
  morph : T R → R
  unit_comm : morph ∘ pure = id
--  TODO : morph_comm : morph ∘ (T morph) = blah blah

-- Lean can't infer that the monad in the args for select_aug is the same in the premises, so we need to give it hints

def monadmap (α β : Type u) (T: Type u → Type v) (f : α → T β) [Monad T] : T α → T β := λ m => bind m f
def monadfunctormap (T: Type u → Type v) (f : α → β) [Monad T] : T α → T β :=
λ x => bind x (Function.comp pure f)

def cont_rew_aug [Monad T] (f : select_aug (T := T) R X) (γ : X → R) [Algebra T R] : R := Algebra.morph ((monadfunctormap T γ) (f γ))
def cont_rew_aug_fn [Monad T] (f : X → select_aug (T := T) R Y) (γ : Y → R) [Algebra T R] : X → R := λ x => cont_rew_aug (T := T) (f x) γ  

def select_aug.unit [Monad T] (R : Type) : X → select_aug (T := T) R X := 
λ x => (λ _ => pure x)
-- TODO: Clean this s*** up
def select_aug.bind [Monad T] (R : Type) [Algebra T R]  : (X → select_aug (T := T) R Y) → select_aug (T := T) R X → select_aug (T := T) R Y :=
  λ f => λ F γ => let f' := cont_rew_aug_fn (T := T) f γ 
                  let F'' := F f' 
                  let lm := λ x => f x γ 
                  let lift := monadmap X Y T lm
                  lift F''

instance [Monad T] [Algebra T R] : Monad (select_aug (T := T) R) where
  pure := select_aug.unit R
  bind x f := select_aug.bind R f x

-- Writer Monad.

def writer [Monoid R] (X : Type) := R × X

example : writer (R := Nat) Nat := ⟨1,2⟩

def writer_unit [Monoid R] : X → writer (R := R) X := λ x => ⟨One.one , x⟩
def writer_bind [Monoid R] : (X → writer (R := R) Y) → writer (R := R) X → writer (R := R) Y := 
λ f x => let ⟨r , y⟩ := f x.2 ; ⟨Mul.mul x.1 r , y⟩    

-- run these #evals to see the writer monad in action
-- #eval writer_unit (R := Int) 2
-- #eval writer_bind (R := String) (λ x => ⟨toString x , -12⟩) ⟨"the number is " , 2*2⟩ 

instance [Monoid R] : Monad (writer (R := R)) where
 pure := writer_unit
 bind x f := writer_bind f x

-- selection monad augmented with writer
instance [Monoid M] [Algebra (writer (R := M)) R]: Monad (select_aug (T := writer (R := M)) R) where
  pure := select_aug.unit R
  bind x f := select_aug.bind R f x

/-
We introduce *barycentric* algebras, which are a commutative monoid R equipped with binary probabilistic choice functions [0,1] → R² → R where certain probabilistic inequalities hold.
I'm too lazy to implement the interval [0,1] (as *reals aren't in mathlib4 yet!!!*) so I'm just working with Rats, courtesy of Mario.
-/

class Barycentric_Algebra (R : Type) where
  choice_p : Rat → R → R → R
  left_unitp x y : choice_p 1 x y = x
  id p x : choice_p p x x = x
  invert p x y : choice_p p x y = choice_p (1 - p) y x
  distr p q x y z : choice_p q (choice_p p x y) z = choice_p (p * q) x (choice_p (((1 - p) * q)/(1 - (p * q))) y z)

class Barycentric_Comm_Monoid (R : Type) where  
  cm : CommMonoid R
  ba : Barycentric_Algebra R
  distr p x y z : Mul.mul x (ba.choice_p p y z) = ba.choice_p p (Mul.mul x y) (Mul.mul x z)

class Discrete_Probability_Distr (X : Type) where
  fn : X → Rat
  finite_zeros : Finite (Subtype (λ x => fn x ≠ 0))
  sum_to_one : 




