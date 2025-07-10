import Game.Metadata

World "Spinoza"
Level 1

Title ""

Introduction
"
**ベネディクトゥス**: ほら, 見てください. これはあなたのために準備したものです. 
"
Statement (A B : Prop) (h : A → ¬ B) (k : A ∧ B) : False := by
  Hint "**あなた**: まずはこのAND（`∧`）を分解する必要がありそうですね. "
  obtain ⟨h₁, h₂⟩ := k
  Hint (strict := true) "
    **あなた**: そして今…

    **ベネディクトゥス**: …適切な中間結果を準備するべきです. 

    **Robo**: そうだ！また`have`を使ってみて！具体的には`have g : ¬ B`！"
  have g : ¬ B
  · Hint "
      **あなた**: え? 今これを正しいと仮定しただけ? 

      **Robo**: いや, 使う前にこれを証明する必要がありますよ. "
    Hint (hidden := true) "**Robo**: `apply`が役立つはず"
    apply h
    assumption
  Hint "**あなた**: そして, 2つの仮定が矛盾する場合はどうするんでしたっけ? 

  **Robo**: `contradiction`です. "
  contradiction

Conclusion "**ベネディクトゥス**: 良さそうですね！"

--NewTactic «have»  -- now introduced very briefly in Implis
DisabledTactic «suffices» tauto
