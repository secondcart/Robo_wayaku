import Game.Metadata
import Game.Levels.Prado.L09_ExistsUnique

World "Prado"
Level 10

Title ""

Introduction
"ようやく屋上テラスに到着しました. 
しかしGuinoはすでに建築の詳細を説明するのを諦めています. 
景色は悪くありません. 

**Robo** *(あなたに)*: そろそろ準備ができたと思う. 
"

namespace Nat

Statement : ∃! (p : ℕ), Nat.Prime p ∧ Even p := by
  use 2
  simp
  constructor
  · decide
  · intro p hp h
    Hint (hidden := true) "**Robo**:
    もう一度, これまでに証明した命題をよく見てみよう. "
    rw [even_iff_two_dvd] at h
    rw [prime_def] at hp
    obtain ⟨h2, hprime ⟩ := hp
    apply (hprime 2) at h
    obtain h | h:= h
    · contradiction
    · symm
      assumption

TheoremTab "ℕ"

Conclusion "
**あなた**: やったー!  でも誰が彼に報告する? 

**Robo**: やめておいた方がいいかも. どうやら彼は, 
博物館がこのまま空っぽなのが一番気に入っているみたいだ. 

あなたたちは丁寧にガイドツアーにお礼を言い, この地の氷の芸術に深く感銘を受けた様子を見せて, さらに飛び立っていきました. "
