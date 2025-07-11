import Game.Metadata

World "Logo"
Level 11

Title "Und"

Introduction
"
蛇のような列も, 徐々に短くなっていきます. 次の編み物をしているFormalosophenが, 次のような要望を書いた紙を持っています.
"

Statement (A B C : Prop) (h : A ∧ (B ∧ C)) : B := by
  Hint "
    **あなた**: そろそろ仮定を分解する必要がありそうだ.

    **Robo**: はい, その通りです. 最も簡単な方法は`obtain ⟨h₁, h₂⟩ := {h}`を使うことです.

    **あなた**: 待って, どうやって書けばいいんだっけ?

    **Robo**: 角括弧は`\\<`と`\\>`で書くか, まとめて`\\<>`と書きます.
    h₁は単に`h\\1`と書けます. でも`h₁`や`h₂`の代わりに他の名前を使っても構いません.
    例えば`obtain ⟨hA, hBC⟩ := {h}`のように. "
  Branch
    obtain ⟨_h₁, _h₂⟩ := h
    Hint "**Robo**: だいぶ良くなってきました! もう一度やってみましょう! "
  obtain ⟨_h₁, g, _h₃⟩ := h
  Hint (hidden := true) "**Robo**: あなたはその証明を*仮定*の中に持っています. "
  assumption

Conclusion
"
**Robo**: ちなみに, これは直接ネストして書くこともできました:
`obtain ⟨h₁, h₂ , h₃⟩ := h`.
"

NewTactic obtain
DisabledTactic tauto
