import Game.Metadata

World "Piazza"
Level 7

Title "Antisymmetrie"

Introduction
"
**集合**: そして私はこの同値性が好きです。
"

open Set

/---/
TheoremDoc Set.Subset.antisymm_iff as "Subset.antisymm_iff" in "Set"

Statement Set.Subset.antisymm_iff {α : Type} {A B : Set α} : A = B ↔ A ⊆ B ∧ B ⊆ A := by
  Hint "**あなた**: はい、一度そう習った覚えがあります
  – 2つの集合が相互に含まれている場合、それらは等しいです。"
  Hint (hidden := true) "**ロボ**: わかりませんが、`constructor`から始めると思います。"
  constructor
  · intro h
    Hint (hidden := true) "**ロボ**: `{A}`を`{B}`に置き換えてみてください。"
    rw [h]
    tauto
  · intro h
    Hint (hidden := true) "**ロボ**: ここからは先ほどのパターンが再び当てはまるはずです。"
    ext i
    tauto

NewDefinition Subset

TheoremTab "Set"

Conclusion ""
