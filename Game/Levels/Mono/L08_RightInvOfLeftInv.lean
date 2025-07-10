import Game.Levels.Mono.L07_SuccHasLeftInv

World "Mono"
Level 8

Title ""


Introduction ""

open Function Set

-- This is in mathlib: #check rightInverse_of_injective_of_leftInverse
Statement {A B : Type} {f : A → B} {g : B → A} (injf : Injective f)
    (hL : LeftInverse f g) : RightInverse f g := by
  Hint "**あなた**: ここには何が書いてあるの? 

  **Robo**: 射影`f`が単射で, 写像`g`に対して左逆元である場合, 同じ写像に対して右逆元でもあります. 
  "
  intro x
  apply injf
  rw [hL]
