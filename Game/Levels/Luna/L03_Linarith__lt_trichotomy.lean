import Game.Metadata


open Nat

World "Luna"
Level 3

Title ""

Introduction
"
**リナ**: これで試してみて！
"

/--
Wird typischerweise mit `obtain` verwendet, um in einem Beweis die drei Fälle `x < y`, `x = y` und `x > y` zu unterscheiden:

```
obtain h | h | h := lt_trichotomy x y
```
-/
TheoremDoc lt_trichotomy as "lt_trichotomy" in "≤"


Statement lt_trichotomy: ∀ a b : ℝ, a < b ∨ a = b ∨ b < a := by
  intro a b
  Hint (strict := true)"
    **あなた**: 場合分け? ? 

    **Robo**: はい, 試してみてください. 例えば最初に`by_cases h_leq : {a} ≤ {b}`, 次に`by_cases h_lt : {a} < {b}`で. 
  "
  by_cases h_leq : a ≤ b
  · by_cases h_lt : a < b
    · left
      assumption -- or linarith
    · right
      left
      Hint "
        **あなた**: で, どうする? 

        **リナ** (*勝利の表情*): `linarith`だよ！
        "
      linarith  -- WANT LINARITH in this exercise!
  · right
    right
    linarith -- WANT LINARITH in this exercise!

NewTactic linarith

TheoremTab "≤"

Conclusion "
  **リナ**: ところで, 単に`apply lt_trichotomy`と言うこともできたんですよ. 
"
