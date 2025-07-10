import Game.Levels.Mono.L06_StrictMono

World "Mono"
Level 7

Title ""

Introduction ""

open Function Nat

Statement : HasLeftInverse succ  := by
  Hint "**あなた**: どうやら, 写像 `n ↦ n + 1` が左逆元を持つと主張されているようです。
  そこで, 単純に `n ↦ n - 1` という写像を考えればいいのですが… `n = 0` の場合はうまくいきません。

  **ロボ**: `if … then … else` を使って場合分けしてもいいけど, 実際にはそれすら必要ありません。Leanでは `0 - 1` も `ℕ` に属します。

  **あなた**: え…！？

  **ロボ**: はい。これは単純に `0` と定義されています。"
  Branch
    use (fun n ↦ if 0 < n then n - 1 else 0)
    Hint "**ロボ**: 良さそうですね。でも, この分岐は全く不要です。
    単に `n ↦ n - 1` を使っても大丈夫ですよ。試してみて！"
  Branch
    use (fun n ↦ if 0 < n then n - 1 else 0)
    unfold LeftInverse
    Hint "**ロボ**: 良さそうですね。でも, この分岐は全く不要です。
    単に `n ↦ n - 1` を使っても大丈夫ですよ。試してみて！"
  Branch
    let g := (fun n ↦ if 0 < n then n - 1 else 0)
    Hint "**ロボ**: 良さそうですね。でも, この分岐は全く不要です。
    単に `n ↦ n - 1` を使っても大丈夫ですよ。試してみて！"
  use (fun n ↦ n - 1)
  simp [LeftInverse]


Conclusion "
  **あなた**: まだショックを受けています。
  ここでは数学をやっていると思っていたのに, 
  なぜ `0 - 1` が `0` になるんですか？

  **ロボ**: 見方の問題です。あなたは `n ↦ n - 1` を正の自然数でのみ定義された写像と考えています。
  Leanでは `n ↦ n - 1` は全ての自然数で定義された写像で, `0` を `0` に送ります。
  なぜでしょう。結局この写像は正の数にしか適用されないので, あなたの解釈とLeanの解釈は幸いにも一致しています。
"
