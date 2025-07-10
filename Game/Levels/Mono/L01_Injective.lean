import Game.Metadata


World "Mono"
Level 1

Title ""

Introduction
"
最上階には実際、再び多くの形式哲学者が集まっています。
彼らはあなた方を喜んで歓迎し、すぐに本題に入ります。
"
open Set Function

Statement :
    let f := fun (n : ℤ) ↦ n + 3
    Injective f := by
  Hint "
    **Robo**: `Injective` はあなたが期待するように定義されています: `∀ \{a b : U}, f a = f b → a = b`。
    私を信用しないなら、`unfold`で簡単に確認できます。"
  Hint (hidden := true) "
    **Robo**:  `intro a b`から始めてみてはどうでしょう。
  "
  Branch
    unfold Injective
  intro a b
  Branch
    simp [f]
  intro ha
  Hint (hidden := true)
  "**Robo**: 今こそ`{f}`の定義を使って仮定`{ha}`を簡略化すべきだと思います。"
  simp [f] at ha
  assumption

NewDefinition Function.Injective
TheoremTab "Function"

Conclusion "形式哲学者たちは、あなた方の仕事をよくやったと評価しています。"
