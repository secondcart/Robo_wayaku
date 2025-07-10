import Game.Metadata


World "Epo"
Level 6

Title "Every function with nonempty fibres has a right inverse."


Introduction ""


open Function

Statement {A B : Type} (f : A → B) (nonempty_fibre : ∀ b : B, ∃ (x : A), f x = b) :
    HasRightInverse f := by
  Hint "**Du**: 何だか選択公理の匂いがするな。

  **Robo**: その通り。`choose`を覚えてる？
  ここで`choose`が真価を発揮するよ。
  `choose g hg using nonempty_fibre`を試してみて。"
  choose g hg using nonempty_fibre
  use g
  assumption

-- NewTactic choose  -- wird nun bereits in Quantus eingeführt
