import Game.Metadata

open Finset

World "Babylon"
Level 2

Title ""

Introduction "一緒に次の塔を見てみましょう. "

Statement (I : Finset ℕ) : ∑ i ∈ I, 2 = 2 * card I := by
  Hint (hidden := true) "**あなた**: また`simp`を使う? "
  simp
  ring
