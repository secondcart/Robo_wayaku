import Game.Metadata

World "Quantus"
Level 1

Title "Natürliche Zahlen"

Introduction "表面には次のように書かれています。"

Statement : Nonempty ℕ := by
  Hint "**あなた**: 自然数が存在することを示せばいいんですか？

  **ロボ**: その通りです。`use _`を使って任意の自然数を指定してください。"
  use 0

Conclusion "紙を裏返します。"

NewTactic use
NewDefinition Nonempty
