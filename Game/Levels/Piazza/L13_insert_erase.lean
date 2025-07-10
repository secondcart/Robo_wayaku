import Game.Metadata

World "Piazza"
Level 13

Title ""

Introduction "
  **フィン**: さて, みんなどう思う? これでまた全員のピスタチオが家に帰れたかな? 
"

/---/
TheoremDoc Finset.insert_erase as "insert_erase" in "Set"

namespace Finset
open Classical -- otherwise need `[h : DecidableEq A]` in the statement
               -- open scoped Classical also works in vscode and compliles without error,
               -- but somehow leads to error in this level when deployed locally with npm start
Statement insert_erase {A : Type} {s : Finset A} {a : A} (h : a ∈ s) :
  insert a (Finset.erase s a) = s := by
  ext b
  simp
  Hint (hidden := true) "
    **フィン**: {b} = a かどうかで場合分けしてみたらどうかな
  "
  Branch
    constructor
    Hint "**フィン**: そうそう, そのやり方でいけるよ"
    · intro h
      obtain h₁ | ⟨ h₂, h₃ ⟩ := h
      rw [← h₁] at h
      assumption
      assumption
    · intro hb
      by_cases heq: b = a
      left
      assumption
      right
      constructor
      assumption
      assumption
  by_cases heq : b = a
  · rw [heq]
    tauto
  · simp [heq]

TheoremTab "Set"

Conclusion "子供たちは笑いながら, あなたたちを囲むように輪を作り, 二人には理解できない言葉で歌を歌います. そして走り去っていきます. 

**Robo**: 私たち, もう飛び立てるみたいだね"
