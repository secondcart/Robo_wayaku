import Game.Metadata

World "Quantus"
Level 8

Title "push_neg"

Introduction
"
**Robo** 待っている間, 量化子と否定の関係について少し説明しましょう. すぐに必要になる気がします.
"


open Function

Statement {X : Type} (P : X → Prop) :
    ¬ (∃ x : X, P x) ↔ ∀ x : X, ¬ P x := by
  Hint "
    **あなた** この`{P}`って何?

    **Robo** `{P}`は「述語」です. `{X}`型のオブジェクトに関する命題です.
              例えば`{X}`が自然数の型だとしましょう.
              そして`{P} x`は次のような命題かもしれません:
              自然数`x`は偶数である. または: `x`は7つの素因数を持つ. または: `x`は
              Roboのお気に入りの数字である. または…

    **あなた** もう大丈夫, わかった気がする. `{P}`は要するに, 要素`x : {X}`を取って
    命題を返す写像みたいなものだね.

    **Robo** そう, そんな感じです.

    **あなた** よし. それならこの命題の意味もほぼ明らかだ.
            で, 今からLeanでこれを証明する方法を教えてくれるんだよね?

    **Robo** その通り. 必要なのは`push_neg`です. "
  Branch
    constructor
    intro h
    Hint (hidden := true) "
      **Robo** `push_neg`は左から右に作用します. ここではゴールには適用できませんが,
      `{h}`には適用できます. "
    push_neg at h
    assumption
    intro h
    push_neg
    assumption
  push_neg
  rfl

NewTactic push_neg
DisabledTactic tauto

Conclusion
"
**Robo** よくできました. 内部的に`push_neg`は2つの補題を使っています:

 - `not_exists (P : X → Prop) : ¬ (∃ x, P x) ↔ ∀ x, (¬ P x)`
 - `not_forall (P : X → Prop) : ¬ (∀ x, P x) ↔ ∃ x, (¬ P x)`

最初の補題が, あなたが今証明した命題です.

**あなた** なるほど. つまり私はこの命題を, それを使いながら証明したわけだ…

**Robo** (ニッコリ) とにかく`push_neg`を覚えておいてください.
"
