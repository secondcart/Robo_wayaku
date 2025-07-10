import Game.Metadata

World "Piazza"
Level 6

Title ""

Introduction
"
**Ext**: 私は*この*方程式が好きです。
"

open Set

Statement (A B : Set ℕ) :
    univ \ (A ∩ B) = (univ \ A) ∪ (univ \ B) ∪ (A \ B) := by
  Hint (hidden := true) "**ロボ**: 今回はまた単純に`ext`を使えばいいよ。"
  ext i
  Hint (hidden := true) "**ロボ**: そしてもちろん今度も`simp`だ。"
  simp
  tauto

NewDefinition SDiff
TheoremTab "Set"

Conclusion "
  **あなた** *(ロボに向かって)*: どうしてextってextって言うの？

  **ロボ**: 少年がどこから名前を取ったかなんて, 私に分かるわけないでしょう？

  **あなた**: いや, ここの`ext`のことだよ！

  **ロボ**: ああそう。2つの集合が同じ要素を持つとき, そしてそのときに限り等しいという原理を, 
  論理学者は*外延性*と呼んでいます。そして形式哲学者たちはおそらく, 
  長すぎるからって*ext*にしたんでしょうね。
"
