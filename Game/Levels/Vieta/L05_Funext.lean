import Game.Metadata


World "Vieta"
Level 5

Title "" -- "funext"


Introduction
"
Vietaは慎重に周りを見回した後, 立ち止まった。
彼は静かに次の紙をあなたに手渡す。
"

open Function

Statement :
    let f := fun (x : ℤ) ↦ x ^ 2;
    let g := fun x ↦ f (-x);
    f = g := by
  Hint "**あなた**: 定義によれば, 2つの関数が等しいとは, すべての要素に適用した時に同じ値を返すことですよね…

**ロボ**: その原理には`funext`という戦略があります。
`funext x`を使うと, 任意の`x`を選び, 証明目標を`f = g`から`f x = g x`に変更できます。"
  funext x
  Hint (hidden := true) "**ロボ**: 念のため, `ring`はローカル定義を見通します。"
  ring

OnlyTactic funext ring
NewTactic funext
TheoremTab "Function"

Conclusion ""
