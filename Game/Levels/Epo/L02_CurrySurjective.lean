import Game.Metadata


World "Epo"
Level 2

Title ""

Introduction ""

open Function Nat

#check ne_comm

Statement {A B : Type} (f : ℕ → A → B) : ¬ Surjective f ↔ ∃ g : A → B, ∀ n, g ≠ f n := by
  Hint "
  **あなた**: `ℕ → A → B`…この連続した矢印はどう読むのですか？

  **ロボ**: これは`ℕ → (A → B)`と読みます。自然数`ℕ`からAからBへの写像の集合`A → B`への写像です。これは、あなたがここで示すべきことを読み進めると明らかになります。"
  Hint (hidden := true) "
  **ロボ**: `constructor`で始めるか、`unfold Surjective`で始めてから`push_neg`が役立つかどうか確認すると良いでしょう。"
  Branch
    constructor
    · intro h
      simp [Surjective] at h
      push_neg at h
      obtain ⟨w, hw⟩ := h
      use w
      intro n
      Hint "
      **ロボ**: `ne_comm`が役立つかもしれません。
      `ne_comm`の主張は`a ≠ b ↔ b ≠ a`です。"
      rw [ne_comm]
      apply hw
    · intro ⟨g, hg⟩
      intro hf
      obtain ⟨n, hn⟩ := hf g
      apply hg n
      symm
      assumption
  unfold Surjective
  push_neg
  Hint "
  **ロボ**: `ne_comm`が役立つかもしれません。
  `ne_comm`の主張は`a ≠ b ↔ b ≠ a`です。
  "
  Hint (hidden := true) "
  **ロボ**: 多くの量化子があるため、ここでは`rw [ne_comm]`は機能しません。
  代わりに`simp [ne_comm]`を試してみてください。
  "
  simp [ne_comm]

/---/
TheoremDoc ne_comm as "ne_comm" in "Logic"
NewTheorem ne_comm
-- NewConcept: Multivariate functions
