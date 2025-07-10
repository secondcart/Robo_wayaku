
import Game.Metadata

World "Piazza"
Level 1

Title ""

Introduction
"
**Fin**:  ええ, もちろん。例えばこれなんかどうでしょう。
"

open Set

Statement : 1 ∈ ({1, 6, 4} : Set ℕ) := by
  Hint "
    **あなた**: これで合ってる？

    **Robo**: たぶんね。かなり*トートロジー*的に見えるでしょ？
    "
  tauto

NewDefinition Mem Set
TheoremTab "Set"

Conclusion "
**セット**: 君たちも集合論に少し詳しいんだね？

**Robo**: まあ, *ちょっと*ね。
"
