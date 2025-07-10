import Game.Metadata
import Game.Levels.Prado.L01_prime_two

World "Prado"
Level 2

Title ""

Introduction
"
**あなた** *(小声で)*: Robo, 彼に言った方がいいと思う？

**Robo**: `2`が唯一の偶数の素数だってこと？
証明を見せないと信じてくれないだろうね。

**あなた**: それって私たちでも示せるんじゃない？ あなたはその言語知ってるでしょ。
試してみよう。例えば「`a`が`b`を割り切る」ってどう書くの？

**Robo**: いいだろう。「`a`が`b`を割り切る」は`a ∣ b`と書くんだ。縦棒は`\\|`か`\\dvd`で書かないといけない。例えばこの問題を試してみて。
"

-- This is `Nat.dvd_add`, but currently that statement is not needed anywhere.
-- /---/
--TheoremDoc Nat.dvd_add as "dvd_add" in "ℕ"

namespace Nat

Statement {a b c : ℕ} (h : a ∣ b) (g : a ∣ c) : a ∣ b + c := by
  Hint "
  **Robo**: `a ∣ b`はもちろん`∃ k, b = a * k`と定義されている。
  最初はどこでも明示的に書き出した方がいい:
  ```
  rw [dvd_iff_exists_eq_mul_left] at *
  ```
  "
  rw [dvd_iff_exists_eq_mul_left] at * -- optional
  Hint (hidden := true) "
    **あなた**: それで次は`obtain`と`use`で進めるの？

    **Robo**: そうだよ。次は`obtain ⟨x ,hx⟩ := _`などで仮定を分解する"
  obtain ⟨x, h⟩ := h
  obtain ⟨y, g⟩ := g
  Hint (hidden := true) "**Robo**: 今度は`use _`で`{b} + {c} = {a} * _`となるような数を指定するんだ"
  use x + y
  Hint (hidden := true) "**Robo**: 少し書き換えれば`ring`が使えるはずだ"
  rw [h, g]
  Branch
    linarith  -- works here, but omega does not!
  ring

/--
`a ∣ b` bedeutet `∃ k, b = a * k`.

**Warnung**: Die Symbole `∣` (`\\dvd`) und `|` (ASCII vertikaler Strich) sind zwei unterschiedliche
Zeichen! Das erste wird ausschließlich für „teilt“ verwendet, das andere kommt zum Beispiel in der
Syntax `obtain h₁ | h₂ := h` vor.
-/
DefinitionDoc Dvd.dvd as "· ∣ ·"

NewDefinition Dvd.dvd

/---/
TheoremDoc dvd_iff_exists_eq_mul_left as "dvd_iff_exists_eq_mul_left" in "ℕ"
NewTheorem dvd_iff_exists_eq_mul_left

TheoremTab "ℕ"

Conclusion "**ギノ**: 何を囁いてるんだ？

**あなた**: ああ, 別に。Roboが素数とは何かを思い出させようとしてるだけだよ。

ギノがあなた方の証明を見ている。

**ギノ**: 悪くない, 悪くない。でももう少し進もう。
博物館はまだ空いてるけど完成してる。本当に良くできてるんだ。ほら, こちらへ来て見て！"
