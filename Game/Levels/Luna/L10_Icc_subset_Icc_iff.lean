import Game.Metadata

World "Luna"
Level 10

Title ""

Introduction "
**Ritha**（*Linaに向かって*）：お願い, 私にも一つ質問させて……

**Lina**：わかった, 一つだけね……でもまた`omega`はダメよ! 

Rithaは大きな目をして, Linaに懇願するように見つめる. 

**Lina**：どうしても*絶対に*必要なのなら. でも急いで! もう本当に時間がないの! 
"


/---/
TheoremDoc Finset.Icc_subset_Icc_iff as "Icc_subset_Icc_iff" in "≤"
-- Note that mathlib's theorem is more general; here we restrict to ℕ

namespace Finset
Statement Icc_subset_Icc_iff (a₁ b₁ a₂ b₂ : ℕ) :
a₁ ≤ b₁ →  (Icc a₁ b₁ ⊆ Icc a₂ b₂ ↔ a₂ ≤ a₁ ∧ b₁ ≤ b₂) := by
  -- unfold Icc -- optional
  Hint (hidden := true) "
    **Robo**: ここではまた`subset_iff`が役立つかもしれません. どうしてもわからなかったら, `simp`を試してみて. 
    "
  rw [subset_iff]
  simp
  intro h₁
  -- omega -- still fails here
  constructor
  · -- omega -- still fails here
    intro h
    Hint (hidden := true) "
      **Robo**: 仮定`{h}`を何らかの形で利用する必要があります. 
      `{h}`を不等式`a₁ ≤ b₁`や`a₁ ≤ a₁`に適用してみてはどうでしょう! 
      （不等式`a₁ ≤ a₁`は`have`を使って表現するのがベストです）
    "
    apply h at h₁
    have : a₁ ≤ a₁ := by rfl  -- briefly introduced in Implies, so that Luna does not depend on Spinoza
    apply h at this
    omega
  · omega

Conclusion ""
