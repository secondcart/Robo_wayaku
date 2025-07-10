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
    **あなた**: これは何ですか?  `A` は「型」? 

    **Roboット** `A` は単に集合と考えてください…

    **あなた** …仮定 `h` によると空ではない? 

    **Roboット** その通り. 

    **あなた** そして, `A` に要素が存在することを示せばいい? 

    **Roboット** 正解です. 

    **あなた** それは仮定から直接導かれるのでは? 

    **Roboット** これは `obtain` で「分解」できる仮定です. 
    `obtain ⟨a⟩ := h` を試してみてください. 
  "
  obtain ⟨a⟩ := h
  use a

NewDefinition Exists

Conclusion "控えめな拍手が送られます. 形式哲学者たちはひそひそ話をしています. "
