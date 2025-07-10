import Game.Levels.Mono.L05_StrictMono

World "Mono"
Level 6

Title ""

Introduction "どうやら誰かが`StrictMono.injective`が予測されていたことに気づいたようです. 
今, 彼らはその証明を見たいと思っています. "

open Set Function

Statement StrictMono.injective {f : ℤ → ℤ}
    (hf : StrictMono f)  : Injective f := by
  Hint (hidden := true) "
    **Robo**: まずは古典的に, `Injective f`から変数と仮定を導入してみては？
  "
  intro a b h
  Hint (hidden := true) (strict := true)"
    **Robo**: 次に場合分けをしてみましょう. `lt_trichotomy`を覚えていますか？
  "
  obtain hlt | heq | hgt := lt_trichotomy a b
  · apply hf at hlt
    rw [h] at hlt
    linarith
  · assumption
  · -- proof by symmetry (e.g. `wlog` or `swap`)
    apply hf at hgt
    rw [h] at hgt
    linarith

DisabledTheorem StrictMono.injective
