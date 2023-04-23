import Std
import Abaplot.monads.strength

/-
  Some monad implementation. Mostly a warm-up for me implementing abaplot.
  Every monad here is outlined in section 2 and 4 of the paper.
-/

/-
  selection monad
  the selection monad select_R(X) of some reward type R and input type X
  is of type (X → R) → X. 
  intuitively, this takes in a selection function f : X → R
  and returns a selection in X. 
-/

def select (R X : Type) := (X → R) → X

example : select Nat Nat := λ f => f 0

/- 
  reward continutations 
  since the selection monad returns a selection for each function,
  for any reward function γ : X → R, we can pass it into the selection monad
  to get a value of type X. we can then pass this back into γ to get the
  associated function value.
-/

def rew_of_opt (f : select R X) (γ : X → R) := γ (f γ)
notation:51 "R (" monad:52 "|" fn:52 ")" => rew_of_opt monad fn

-- Showing that select is an actual monad
def select.unit {R : Type} : X → select R X := λ x => (λ _ => x)
-- We write bind as a Kleisli extension to accurately reflect paper
def select.bind {R : Type} : (X → select R Y) → select R X → select R Y :=
  -- fn : gives an element of R corresp. to each X
  -- opt : since fn is a function X → R, we can pass it through F
  -- this is intuitively the "best choice" for X wrt F; we can now
  -- pass this through f to get the "best selection" (Y → R) → Y. 
  λ f => λ F γ => let fn := λ x => R ((f x) | γ) 
                  let opt := F fn
                  (f opt) γ 

-- The selection monad needs an instantiated reward type (usually ℤ or ℝ)
instance : Monad (select R) where
 pure := select.unit
 bind x f := select.bind f x

-- for f : X → select R Y, we write f†ₛ for its Kleisli extension 
notation:1024 arg:1024 "†ₛ" =>  select.bind arg

-- We can define the strength of the selection monad
-- rather easily.
def st_select : strength X Y (select R) := λ (x, F) => (λ γ => (x, F (λ y => γ (x,y))))

instance : StrongMonad (select R) where
  strong := st_select

notation:71 "stₛ" args:72 => st_select args