import Game.Levels.Samarkand.L03_SurjectiveRange


World "Samarkand"
Level 4
Title "" -- ""

open Set

Introduction "
  **アラプカ**:  これも手伝ってもらえるかな? 
  "
/---/
TheoremDoc Function.Surjective.image_preimage as "Surjective.image_preimage" in "Function"

namespace Function
Statement Surjective.image_preimage {A B : Type} {f : A → B} (hf : Surjective f) (T : Set B) :
f '' (f ⁻¹' T) = T := by
  Hint "
    **あなた**:  これさっきもやったんじゃない? 

    **Robo**:  いいえ. さっきは包含関係 `image_preimage_subset` だけでした：
    ```
    f '' (f ⁻¹' T) ⊆ T
    ```
    今回は等号を示しますが, `f` が全射であるという追加の仮定があります. 
  "
  ext b
  simp
  constructor
  · apply image_preimage_subset -- Lvl 1
  · intro hb
    obtain ⟨a, ha⟩ := hf b
    use a
    constructor
    · rw [ha]
      assumption
    · assumption

Conclusion "
  **アラプカ**:  本当に助かります! 
"
