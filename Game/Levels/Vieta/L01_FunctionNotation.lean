import Game.Metadata

World "Vieta"
Level 1

Title "Anonyme Funktionen"

Introduction "**Vieta:** さあ, 何か見せましょう…

彼はあなたに紙切れを渡す。
"

Statement (f : ℤ → ℕ) (n : ℤ): f n ≥ 0 := by
  Hint "**あなた**: `f`は`ℤ`から`ℕ`への写像に見えますね。

  **Robo**: はい, その通りです。そして`f n`は$f(n)$の表記です。ただしLeanでは括弧を省略します。括弧を使いたい場合は, 必ず括弧の周りにスペースを入れる必要があります。例えば`f (n)`のように。

  **あなた**: わかりました, 覚えておきます。でもここでの写像はℕの値しか取らないので, 実際には示すことは何もないですね。"
  linarith  -- oder simp

Conclusion "
**あなた**: ところで, `→`はさっきまで含意ではなかったですか？

**Robo**: はい, そうです。ここでは両方に同じ記号を使っています。"
