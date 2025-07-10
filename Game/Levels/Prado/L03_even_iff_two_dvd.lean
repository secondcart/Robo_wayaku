import Game.Metadata
import Game.Levels.Prado.L02_dvd_iff_exists_eq_mul_left


World "Prado"
Level 3

Title ""

Introduction
"ギノを博物館で追いかけながら, ロボがさらに課題を出してきます。
"
/---/
TheoremDoc Nat.even_iff_two_dvd as "even_iff_two_dvd" in "ℕ"

namespace Nat

Statement even_iff_two_dvd {a : ℕ} : Even a ↔ 2 ∣ a := by
  Hint (hidden := true) "
    **ロボ**: まずは`rw [dvd_iff_exists_eq_mul_left]`から始めてみよう！
  "
  Branch
    unfold Even
    constructor
    · intro h
      obtain ⟨w, hw⟩ := h
      use w
      rw [hw]
      ring
    · intro h
      obtain ⟨w, hw⟩ := h
      use w
      rw [hw]
      ring
  rw [dvd_iff_exists_eq_mul_left]
  unfold Even
  ring

TheoremTab "ℕ"
