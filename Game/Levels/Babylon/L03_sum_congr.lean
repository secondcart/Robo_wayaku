import Game.Metadata

World "Babylon"
Level 3

Title ""

Introduction
"次に, 長い間何も行われていないように見える空き建築現場に到着します。
看板には次のように書かれています："

open Finset

Statement (I : Finset ℤ) (h : ∀ i ∈ I, (i-1)*i*(i+1) = 0): ∑ i ∈ I, (i-1)*i*(i+1)  = 0  := by
  Hint "
    **あなた**: この仮定は$I \\subseteq \\\{-1,0,1\\}$の複雑なバリエーションのように見えます。
    どうせ大きな合計にはならないでしょう。

    **ロボット**: いいえ。しかし, 指定された結果を得るためには中間ステップが必要です。
    `trans ∑ i ∈ I, 0`と書くことを提案します。合計記号は`\\sum`と書きます。
    "
  trans ∑ i ∈ I, 0
  Hint "
    **ロボット**: その通りです。これで`apply sum_congr`と書くことができます
    - 特に, 同じインデックス集合に対して合計が行われ, 合計される式も一致する場合, 2つの合計は等しくなります。
  "
  apply sum_congr
  rfl
  assumption
  simp

/---/
TheoremDoc Finset.sum_congr as "sum_congr" in "∑ Π"
NewTheorem Finset.sum_congr

TheoremTab "∑ Π"

NewDefinition Sum
