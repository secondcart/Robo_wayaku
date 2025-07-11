import Game.Metadata

World "Piazza"
Level 8

Title ""

Introduction
"
**Sub**: あなたの言う通りです. 
訪問者にもう少し包含について質問してみましょう. 
"

/---/
TheoremDoc Set.subset_iff as "subset_iff" in "Set"

namespace Set

Statement subset_iff {A : Type} {s₁ s₂ : Set A} : s₁ ⊆ s₂ ↔ ∀ {x : A}, x ∈ s₁ → x ∈ s₂ := by
  Hint "**Robo**: これは定義そのものですよ! 

  **Robo** *(あなたへ)*: `tauto`を試してみてください. あるいは直接`rfl`でもいいです. "
  Branch
    tauto
  rfl
end Set

NewDefinition Subset

/---/
TheoremDoc Finset.subset_iff as "subset_iff" in "Set"
NewTheorem Finset.subset_iff


TheoremTab "Set"

Conclusion ""
