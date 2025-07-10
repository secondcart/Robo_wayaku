import Game.Metadata

World "Quantus"
Level 9

Title "PushNeg"

Introduction
"
長い議論の末, フォルマロソフィストたちはついに以下の問題に合意しました。
"

open Nat

Statement : ¬ ∃ (n : ℕ), ∀ (k : ℕ) , Odd (n + k) := by
  Hint "**あなた**: おや。一番左に`¬`がありますね。驚きました…"
  Branch
    unfold Odd
    Hint "
      **ロボ**: この解法は少し難しすぎるようです。
      `Odd`を保持したままにして, 
      最終的に`even_iff_not_odd`を使えるようにした方が良いでしょう！"
  push_neg
  intro n
  Branch
    unfold Odd
    Hint "
      **ロボ**: この解法は少し難しすぎるようです。
      `Odd`を保持したままにして, 
      最終的に`even_iff_not_odd`を使えるようにした方が良いでしょう！"
  Hint "
    **ロボ**: ここで`use`を使って数値を指定し, その後おそらく
    補題`even_iff_not_odd`を使う必要があります。

    **あなた**: 今すぐ`even_iff_not_odd`を適用できますか？

    **ロボ**: いいえ, `rw`は量化子内で書き換えできません。

    **あなた**: ではどうすればいいのですか？

    **ロボ**: それは後で教えます, 大勢の前ではやりません。
    今は`use`で適切な数値を指定してから書き換えることをお勧めします。"
  Branch
    use n + 2
    Hint "**ロボ**: 良い選択です！これで`even_iff_not_odd`が使えます。"
  Branch
    use n + 4
    Hint "**ロボ**: 良い選択です！これで`even_iff_not_odd`が使えます。"
  use n
  Hint "**ロボ**: 良い選択です！これで`even_iff_not_odd`が使えます。"
  rw [← even_iff_not_odd]
  Branch
    tauto
  unfold Even
  use n

-- Note: The following two theorem are just added for completeness.

/-- Statt diesem Theorem kannst du `push_neg` verwenden. -/
TheoremDoc not_exists as "not_exists" in "Logic"
/-- Statt diesem Theorem kannst du `push_neg` verwenden. -/
TheoremDoc Classical.not_forall as "not_forall" in "Logic"

NewTheorem not_exists Classical.not_forall

Conclusion
"
フォルマロソフィストたちは大興奮です。
拍手が収まった後, あなたも一度質問しました。

**あなた**: 誰かフォルマロ宇宙での方向付けを少し手伝ってくれませんか？

**全員**: はい, はい。

**あなた**: 誰が？

質問がまた具体的すぎました。気まずい沈黙。
"
