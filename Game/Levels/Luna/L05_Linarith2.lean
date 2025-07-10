import Game.Metadata


open Nat

World "Luna"
Level 5

Title ""

Introduction "
  **リナ:** 同じ質問をもう一度, 今度はℝで！
"

Statement (l m n x : ℝ) (h₁ : l ≤ m) (h₂ : m ≤ n) : l ≤ x ∧ x ≤ n → ¬ (m ≤ x ∧ x ≤ n) → x ≤ m := by
  Hint "
    **あなた** (*Roboへ*): ここでは`omega`も`linarith`も使えません。

    **Robo**: `linarith`に少し手助けが必要なようです。
    まずは標準的に, 2つの含意を`intro`で解きましょう。
  "
  intro hn hx
  Hint "
    **Robo**: そして, 仮定`{hx}`をもう少し読みやすくします。
    `push_neg at {hx}`を試してみては？
  "
  push_neg at hx
  Hint "
    **Robo**: うーん… `{hx} : m ≤ x → n < x`はまだ最適ではありません。
    しかし, `→`の意味はわかっていますね。`imp_iff_or_not`で`rw`してみましょう！
  "
  --linarith (config := {splitNe := true, splitHypotheses := true}) -- fails
  rw [imp_iff_or_not] at hx
  Hint "
    **Robo**: よし。これで良くなりました。そして, `{hx}`を`obtain`で
    2つの部分に分割できます。
  "
  --linarith (config := {splitNe := true, splitHypotheses := true}) -- fails
  obtain hx | hx := hx
  · linarith
  · linarith

TheoremTab "Logic"

Conclusion ""
