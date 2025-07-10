
import Game.Metadata

World "Piazza"
Level 2

Title ""

Introduction
"
**Mem**: これでどうかな？
"

open Set

Statement : 9 ∈ {n : ℕ | Odd n} := by
  Hint "
    **Robo**: ここは`simp`を使うのが一番簡単だと思うよ。
  "
  simp
  Hint (hidden := true) "
    **Robo**: `decide`を思い出して。
  "
  decide

TheoremTab "Set"

NewTactic simp

NewDefinition setOf

Conclusion ""
