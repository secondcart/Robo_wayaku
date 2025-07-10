import Game.Metadata
import Game.Levels.Quantus

World "Spinoza"
Level 5

Title "Kontraposition"

Introduction
"
**ベネディクトゥス**: では、約束していた問題です。`by_contra`を使わずに*直接*証明してみてください。
"

open Nat

Statement (n : ℕ) (h : Odd (n ^ 2)): Odd n := by
  Hint "
    **ロボ**: `even_square`の補題に帰着させるのが良いと思います。これは基本的に`Odd (n^2) → Odd n`と言っています。
    対偶を取ると`Even n → Even (n^2)`と同値になります。

    **あなた**: その通り。回り道ですが...待って、今は`→`が入っていないですね。

    **ロボ**: `revert`を思い出してください。`revert {h}`で仮定`{h}`を証明目標の含意に戻せます。"
  revert h
  Hint "
    **あなた**: これで対偶法の補題が使えますか？名前は何でしたっけ？

    **ロボ**: 実際には単に`contrapose`と書けます。"
  contrapose
  Hint (hidden := true) "**ロボ**: 今は`even_iff_not_odd`が役立つかもしれません"
  rw [← even_iff_not_odd]
  rw [← even_iff_not_odd]
  Hint "
    **あなた**: 良さそうです。これで古い補題`even_square`が使えます！"
  apply even_square

NewTactic contrapose
DisabledTactic by_contra
TheoremTab "ℕ"

Conclusion "**ベネディクトゥス**: 素晴らしい！これで十分に準備が整いましたね。"
