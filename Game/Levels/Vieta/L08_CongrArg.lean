import Game.Metadata


World "Vieta"
Level 8

Title "" -- "congr_arg"


Introduction
"戦闘音が近づいてきます。Vietaがさらに2枚の紙を渡します。"

open Function

Statement {x y : ℤ} (f : ℤ → ℤ) (h : x = y) :
    let g : ℤ → ℤ := fun x ↦ x + 3;
    f (g 0) = f 3 := by
  Hint "**Robo**: ああ, これは`congr_arg`のケースだ。`x = y`が既に分かっているなら, 
 `apply congr_arg`で`f x = f y`を得られるよ。"
  apply congr_arg
  rfl

/---/
TheoremDoc congr_arg as "congr_arg" in "Function"

OnlyTactic apply rfl
NewTheorem congr_arg -- tactic `congr` would have same effect
TheoremTab "Function"

Conclusion ""
