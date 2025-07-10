import Game.Levels.Samarkand.L05_InjectiveFibre

open Function Set

World "Samarkand"
Level 6

Title ""

Introduction "**アラプカ**: では, これはどうかな? "

Statement {A B : Type} (f : A → B)  (y : B) :
     f ⁻¹' {y} ≠ ∅ ↔ (∃ a, f a = y) := by
  Hint "
   **あなた**: つまり, `b`のファイバーが空でないのは, `b`に原像があるときだけ, ってことですね. 
   またしてもかなり自明なことです. 

   **Robo**: はい, 表記法を除けば. 
   幸い, `eq_empty_iff_forall_not_mem`は既に証明済みです. 
   これを使うには, 不等号を展開する必要があります. 例えば`unfold Ne`で簡単にできます. 
  "
  unfold Ne
  rw [eq_empty_iff_forall_not_mem]
  simp

  Conclusion "
   **アラプカ**: 君たちの言う通りだ. 自分でも気付くべきだった. 
  "
