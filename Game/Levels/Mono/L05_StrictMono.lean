import Game.Levels.Mono.L04_Diagonal

World "Mono"
Level 5

Title "" -- ""

Introduction ""

open Set Function

Statement :
    let f := fun (n : ℤ) ↦ n^3 + (n + 3)
    Injective f := by
  Hint "
    **あなた**: うーん, これは少し難しいですね…

    **ロボ**: 私も今は良いアイデアが浮かびません。

    すると観衆の中から誰かが囁きます: `StrictMono`…

    **ロボ**: ああ, そうですね。`StrictMono.injective`という補題があります:
    厳密単調な写像はすべて単射です。
    そして写像が単調であることを示すための補題もたくさんあります。
    例えば:

    `StrictMono.add` - 2つの厳密単調写像の和は再び厳密単調です

    `Odd.strictMono_pow` - 奇数の`n`に対して`x ↦ x ^ n`は厳密単調です

    これで試してみましょうか？"
  Hint (hidden := true) "**ロボ**: `apply`が使えますよ"
  Branch
    intro a b
    Hint "**ロボ**: この方法は難しすぎるようです。最初からやり直した方が良さそうです！"
  Branch
    intro a b h
    Hint "**ロボ**: この方法は難しすぎるようです。最初からやり直した方が良さそうです！"
  apply StrictMono.injective
  apply StrictMono.add
  · Branch
      have h_odd : Odd 3 := by
        decide
      --exact Odd.strictMono_pow h_odd
      exact h_odd.strictMono_pow
    apply Odd.strictMono_pow
    Hint (hidden := true) "**あなた**: `Odd 3`。これは自明じゃないですか？ちょっと待って！"
    decide
  · Hint "**あなた**: はっ！そしてこの部分はおそらくまた初等的に解けるでしょう"
    Hint (hidden := true) "
      **あなた**: それとも…？

      **ロボ**: いえいえ, できますよ。`unfold`で`StrictMono`の定義を覗いてみてください
    "
    intro a b
    simp

/--
Jede strikt monotone Abbildung (zwischen geeigneten Definitions- und Wertebereichen) ist injektiv.
-/
TheoremDoc StrictMono.injective as "StrictMono.injective" in "Function"

/-- Für ungerades `n` ist `x ↦ x ^ n` strikt monoton.

*Bemerkung*: Hat man `h_odd : Odd n` als Annahme, so kann man statt `Odd.strictMono_pow h_odd` auch einfach `h_odd.strictMono_pow` schreiben.
-/
TheoremDoc Odd.strictMono_pow as "Odd.strictMono_pow" in "Function"

/-- Sind `f` und `g` beide strikt monoton sind, so ist auch `f + g` strikt momonton. -/
TheoremDoc StrictMono.add as "StrictMono.add" in "Function"

NewDefinition StrictMono

NewTheorem StrictMono.injective StrictMono.add Odd.strictMono_pow
TheoremTab "Function"

Conclusion ""
