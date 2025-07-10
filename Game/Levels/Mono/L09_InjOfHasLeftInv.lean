import Game.Levels.Mono.L08_RightInvOfLeftInv

World "Mono"
Level 9

Title ""

Introduction ""

open Function

/---/
-- TheoremDoc Function.HasLeftInverse.injective as "HasLeftInverse.injective" in "Function"
-- Statement Function.HasLeftInverse.injective
Statement {A B : Type} {f : A → B} (h : HasLeftInverse f) :
    Injective f := by
  Hint "
    **あなた**: 左逆元を持つ写像は単射です。聞いたことがあるような気がします…
  "
  intro a a' ha
  obtain ⟨g, hg⟩ := h
  Hint "**ロボ**: たぶん`congr_arg g`で何かできる？"
  Branch
    trans g (f a)
    · rw [hg]
    · rw [ha]
      rw [hg]
  apply congr_arg g at ha
  unfold LeftInverse at hg
  rw [hg a, hg a'] at ha
  assumption

  Conclusion "
    **ロボ**: よくできました！もうすぐ終わりそうですね…
  "
