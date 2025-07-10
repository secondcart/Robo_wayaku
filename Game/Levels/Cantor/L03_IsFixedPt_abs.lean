import Game.Metadata
import Game.Levels.Cantor.L02_CantorPowerset

World "Cantor"
Level 3

Title ""

Introduction
"
**あなた**: でも、これがどう「対角線的」なのかまだ理解できていません。

**カントール**: そうですか？では、ゆっくりと説明しましょう。

彼は再びシルクハットの中を探ります。コンパス。バイオリン。嗅ぎタバコの缶。

**カントール**: いや、違う方法でやりましょう。

彼はもう一度深くシルクハットに手を伸ばし、
紙の束を取り出します。それをあなたに投げます。
あなたはそれらの紙を一枚ずつ見ていきます。
"

Conclusion "
  **カントール**: よくできました！

  彼はいくつかのサボテンでジャグリングを始めましたが、
  どうやらあなたの行動を追っているようです。
"

open Function Set

Statement : ∀ (x : ℝ), IsFixedPt (fun (x : ℝ) ↦ |x|) x ↔ 0 ≤ x := by
-- The function here is simply called `abs` in mathlib,
-- but let's not introduced too much additional notation
-- when it's only needed once.
  Hint "**ロボ**: `|x|`は単に実数`x`の通常の絶対値です。
  `IsFixedPt`の意味は`unfold`で調べられるでしょう。"
  unfold IsFixedPt
  Hint "**あなた**: えっと…

  **ロボ**: `IsFixedPt`はおそらく「固定点である」という意味でしょう。
  いずれにせよ、`IsFixedPt f x`は明らかに`f x = x`を意味します。
  "
  intro x
  constructor
  Hint "**ロボ**: ここまでは順調です。"
  · intro h
    rw [← h]
    --Branch
    --  positivity
    clear h
    Hint "**ロボ**: `simp`を試してみましょう。"
    simp -- only [abs_nonneg]
  · intro h
    -- rw [abs_of_nonneg h]
    Hint (hidden := true) "**ロボ**: `simp`を試してみましょう。"
    simp
    assumption

NewDefinition Function.IsFixedPt absValue
-- absFunction
