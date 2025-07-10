import Game.Metadata

World "Quantus"
Level 7

Title "Für alle"

Introduction "長い混乱の後, 群衆から次の課題があなた方のもとに届きます。"

Statement : ∀ (x : ℕ), (Even x) → Odd (1 + x) := by
  Hint "
    **あなた**: この`∀`はきっと「すべてに対して」という意味だ。

    **ロボ**: そして`\\forall`と書きます。証明目標の`∀ x, …`は, 
    含意のように`intro x`で取り組むことができます。"
  intro x h
  unfold Even at h
  unfold Odd
  choose y hy using h
  use y
  rw [hy]
  ring

NewDefinition Forall

Conclusion
"
再び認めるように頷く。

再び囁き声。
"
