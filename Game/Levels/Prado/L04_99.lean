import Game.Metadata
import Game.Levels.Prado.L03_even_iff_two_dvd

World "Prado"
Level 4

Title ""

Introduction
"ギノは, あなたたちが彼の素晴らしい博物館に全く目を向けていないことに, 少し困惑している様子です. 
彼は無視されていると感じています. あなたたちの注意を引くために, 彼は次の課題を出します. 
"

namespace Nat

Statement : ∃ p : ℕ, Prime p ∧ p ∣ 99 := by
  use 11
  decide

TheoremTab "ℕ"
