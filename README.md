# abaplot (v2)

abaplot is a manifestation of minsung's quest to become *monad minsung* by:

1. implementing the monads in "Smart Choices and the Selection Monad" by Abadi and Plotkin
2. giving a high-level overview of the code through comments.

to check out the implementation, you must have Lean 4 and its supporting CLI tools `elan` and `lake`. then:

1. clone this repo.
2. in the repo, run `lake update` to fetch the correct `lean4, Std4, Mathlib4` versions. in particular, they should be the 2023-04-11 version.
3. open the code in your editor of choice with the Lean LSP (mine is VS Code) and wait for the build. this might take a while.
4. enjoy!

