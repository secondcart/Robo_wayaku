import Game.Metadata

World "Logo"
Level 11

Title "かつ2"

Introduction
"
蛇のような列も, 徐々に短くなっていきます. 次の編み物をしているFormalosophが, 次のような要望を書いた紙を持っています.
"

Statement (A B C : Prop) (h : A ∧ (B ∧ C)) : B := by
  Hint "
    **あなた** そろそろ仮定を分解する必要がありそうだ.

    **Robo** はい, その通りです. 最も簡単な方法は`obtain ⟨h₁, h₂⟩ := {h}`を使うことです.

    **あなた** 待って, どうやって書けばいいんだっけ?

    **Robo**: 角括弧は`\\<`と`\\>`で書くか, まとめて`\\<>`と書きます.
    h₁は単に`h\\1`と書けます. でも`h₁`や`h₂`の代わりに他の名前を使っても構いません.
    例えば`obtain ⟨hA, hBC⟩ := {h}`のように. "
  Branch
    obtain ⟨_h₁, _h₂⟩ := h
    Hint "**Robo** だいぶ良くなってきました! もう一度やってみましょう! "
  obtain ⟨_h₁, g, _h₃⟩ := h
  Hint (hidden := true) "**Robo** あなたはその証明を*仮定*の中に持っています. "
  assumption

Conclusion
"
**Robo** ちなみに, これは直接ネストして書くこともできました.
`obtain ⟨h₁, h₂ , h₃⟩ := h`.

# 今回学んだこと

## Tactics
### obtain
- `obtain`は仮定を構成要素に分解します:

| 前                | tactic               | 後                          |
|:------------------|:-----------------------|:---------------------------|
| `h : A ∧ B`       | `obtain ⟨h₁, h₂⟩ := h` | `h₁ : A`, `h₂ : B`          |
| `h : A ↔ B`       | `obtain ⟨h₁, h₂⟩ := h` | `h₁ : A → B`, `h₂ : B → A`  |
| `h : Nonempty X`  | `obtain ⟨x⟩ := h`      | `x : X`                     |
| `h : ∃ x : X, P x`| `obtain ⟨x, hx⟩ := h`  | `x : X`, `hx : P x`         |
| `h : A ∨ B`       | `obtain h | h := h`   | `h : A`または`h : B`の目標  |
"

NewTactic obtain
DisabledTactic tauto
