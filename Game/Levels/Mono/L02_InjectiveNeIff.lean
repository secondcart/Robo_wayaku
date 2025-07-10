import Game.Levels.Mono.L01_Injective

World "Mono"
Level 2

Title ""

Introduction ""

open Function

Statement (f : ℤ → ℤ  ) (hf : Injective f): f 1 ≠ f (-1) := by
  Hint "**ロボ**: ここでは`Injective f`の定義を使う代わりに、単射性の等価な記述`a ≠ b → f a ≠ f b`を使うことで短縮できます。
  Leanではこれは`Injective.ne_iff`の一部です: 単射写像に対して`f a ≠ f b ↔ a ≠ b`が成り立ちます。"
  rw [Injective.ne_iff]
  Hint (hidden := true) "**ロボ**: `decide`?"
  decide
  assumption

/---/
TheoremDoc Function.Injective.ne_iff as "Injective.ne_iff" in "Function"
NewTheorem Function.Injective.ne_iff
