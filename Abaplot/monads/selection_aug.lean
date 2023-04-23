import Abaplot.monads.selection

/-
  Selection monad augmented with a strong auxiliary monad T
-/

-- We need that the reward type R is a T-algebra, so let's do that.

class Algebra (T : Type → Type) (R : Type) where
  obj : R
  morph : T R → R

-- kleislify simply returns the associated Kleisli map of f wrt monad T
def kleislify [StrongMonad T] (f : α → T β)  : T α → T β := λ m => bind m f
-- kleislify_pure first lifts f : α → β to a function f : α → T(β) 
-- then kleislifys it  
def kleislify_pure [StrongMonad T] (f : α → β)  : T α → T β :=
kleislify (λ a => pure (f a))

-- Now we can define the strong monad.
def select_aug [StrongMonad T] [Algebra T R] (X: Type) := (X → R) → T X


-- The unit is easy enough to define.
def select_aug.unit [StrongMonad T] [Algebra T R] : X → select_aug (T := T) (R := R) X := λ x => λ _ => pure x 

-- We define the reward of opt similarly to that of the selection monad.
def rew_of_opt_aug [StrongMonad T] [Algebra T R] (F : select_aug (T := T) (R := R) X) (γ : X → R) := 
  let Tγ := kleislify_pure γ
  Algebra.morph $ Tγ $ F γ

notation:51 "R (" monad:52 "|" fn:52 ")" => rew_of_opt_aug monad fn

-- The approach to bind is similar to that of the selection monad,
-- except now we can't just naively apply f as it doesn't typecheck.
def select_aug.bind [StrongMonad T] [Algebra T R]  : (X → select_aug (T := T) (R := R) Y) → select_aug (T := T) (R := R) X → select_aug (T := T) (R := R) Y :=
  -- fn, opt are defined identically
  λ f => λ F γ => let fn := λ x => R ((f x) | γ)
                  let opt := F fn
                  -- but we define a new fn' : X → T Y
                  let fn' := λ x => f x γ
                  -- and lift fn' to a function T X → T Y thru kleislify
                  (kleislify fn') opt
      
notation:1024 arg:1024 "†ₛₜ" =>  select_aug.bind arg

instance [StrongMonad T] [Algebra T R] : Monad (select_aug (T := T) (R := R)) where
  pure := select_aug.unit 
  bind x f := select_aug.bind f x

-- select_aug is also strong, assuming T is strong.
-- the strenth of T would be X × T(Y) → T(X × Y) 
def st_select_aug [StrongMonad T] [Algebra T R] : strength X Y (select_aug (T := T) (R := R)) :=
λ (x, F) => λ γ => let rhs := F (λ y => γ (x,y))
                   StrongMonad.strong (x, rhs)

instance [StrongMonad T] [Algebra T R] : StrongMonad (select_aug (T := T) (R := R)) where
  strong := st_select_aug