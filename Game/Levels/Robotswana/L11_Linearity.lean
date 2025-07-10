import Game.Levels.Robotswana.L10_Characterize

--import Game.StructInstWithHoles

set_option tactic.hygienic false

World "Robotswana"
Level 11

Title "" -- "Trace"

Introduction
"
少し離れて立っていると, トレーシーが走り寄ってきて遊び始めます. 面白がりながら様々な課題や項を出し, あなたたちはそれらを十分な速さで組み合わせようとします. 
"

Conclusion "ついにあなたたちは帰路につきます. 
すぐに道に迷ってしまいますが, トレーシーがどうやらついてきていたようで, 草原を横切って船まで案内してくれます. "

open Matrix Fintype

Statement {n : ℕ} {t : ℝ} (A : Matrix (Fin n) (Fin n) ℝ) :
    trace (A - t • 1) = trace A - t • n := by
  Hint "**あなた**: これは明らかに行列のトレースの線形性についてですね. "
  rw [trace_sub]
  rw [trace_smul]
  rw [trace_one]
  Hint "**Robo**: この最後のステップは`card_fin`です. もちろん, 私たちが遊びを楽しんでいなければ`simp`でもできますよ. "
  rw [card_fin]

/---/
TheoremDoc Matrix.trace_one as "trace_one" in "Matrix"

/---/
TheoremDoc Matrix.trace_smul as "trace_smul" in "Matrix"

/---/
TheoremDoc Matrix.trace_sub as "trace_sub" in "Matrix"

/---/
TheoremDoc Fintype.card_fin as "card_fin" in "Set"

NewTheorem Matrix.trace_one Matrix.trace_smul Matrix.trace_sub Fintype.card_fin
OnlyTactic rw
TheoremTab "Matrix"

-- TODO: Move `Fintype.card_fin` to a different planet!
