import Game.Metadata


World "Quantus"
Level 2

Title ""

Introduction
"
裏側には次のように書かれています.
"

Statement (A : Type) (h : Nonempty A) : ∃ a : A, a = a := by
  Hint "
    **あなた** これは何ですか?  `A` は「型」?

    **Robo** `A` は単に集合と考えてください…

    **あなた** …仮定 `h` によると空ではない?

    **Robo** その通り.

    **あなた** そして, `A` に要素が存在することを示せばいい?

    **Robo** 正解です.

    **あなた** それは仮定から直接導かれるのでは?

    **Robo** これは `obtain` で「分解」できる仮定です.
    `obtain ⟨a⟩ := h` を試してみてください.
  "
  obtain ⟨a⟩ := h
  use a

NewDefinition Exists

Conclusion "控えめな拍手が送られます. Formalosophたちはひそひそ話をしています. "
