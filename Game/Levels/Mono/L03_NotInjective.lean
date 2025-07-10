import Game.Levels.Mono.L02_InjectiveNeIff

open Nat

World "Mono"
Level 3

Title ""

Introduction ""

open Function

Statement :
    let f : ℕ → ℕ := fun n ↦ if Even n then n^2 else n+1;
    ¬ Injective (f + f) := by
  Hint "**Du**: 与えられた関数は以下の形式です:
  $$
  f(n) = \\begin\{cases}
    n^2 & \\text\{nが偶数の場合} \\\\
    n+1 & \\text\{それ以外の場合}
  \\end\{cases}
  $$
  そして`f + f`とは何ですか? 

  **Robo**: これは`ℕ → ℕ`の関数で, 各点で`f`の2倍の値を取ります. 
  "
  Hint (hidden := true) "
  **Robo**: まず`Injective`を`unfold`で展開してみましょう. すると`¬ ∀`…と表示されます"
  unfold Injective
  Hint (hidden := true) (strict := true) "**Robo**: `push_neg`を覚えていますか? "
  push_neg
  Hint (hidden := true)"
    **Du** つまり反例を挙げればいいんですよね? 

    **Robo** その通り! どの2つの数字を使いますか? "
  use 2
  use 3
  Hint (hidden := true) "**Robo**: ここでは具体的な値なので, `decide`で解決できるかもしれません"
  decide

TheoremTab "Function"

Conclusion ""
