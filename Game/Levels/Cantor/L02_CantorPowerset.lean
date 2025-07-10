import Game.Metadata
import Game.Levels.Cantor.L01_CantorPowerset

World "Cantor"
Level 2

Title "Cantor's Diagonalargument"

Introduction
"
**カントール**: 注意してください, この議論は実はさらに続くのです！

彼はシルクハットに手を伸ばし, あらゆるものを取り出します. 
古い歯ブラシ, トランプ, 白いウサギ……
ついに皺くちゃのメモ用紙が見つかりました. 

**カントール**: ここに私のノートがあった！ほら！私の有名な対角線論法だ！

彼は紙を広げ, 慎重に一番上の行を引き裂き, 
あなたの方へと舞い降りさせます. 
そして舞台の端から興味津々で覗き込み, あなたの反応を見守ります. 
"

/-
Diagonalgedanke:

Wir betrachten `f : A → Set A` als `f : A → A → Prop`.
Wir betrachten Negation als Selbstabbildung `¬ : Prop → Prop`.
Die Menge `{ a | a ∈ f a }` entspricht der Abbildung `a ↦ f a a `   in `A → Prop`,
die Menge `{ a | a ∉ f a}`  entspricht der Abbildung `a ↦ ¬ (f a a)`.
Wenn `f` surjektiv ist, existiert ein Urbild `a₀` der zweiten Menge,
also `f a₀ = { a | a ∉ f a}`.
Für dieses `a₀` ist dann `f a₀ a₀`, also die Aussage `a₀ ∈ { a | a ∉ f a}` bzw.
`a₀ ∉ f a₀`, ein Fixpunkt von `¬`.
Aber `¬` hat keine Fixpunkte.
-/


open Set Function

Statement {A : Type} : ¬ ∃ f : A → Set A, Surjective f := by
  Hint "**あなた**: これは前に見たことがあります！
  要するに「べき集合は常に元の集合より大きい」ということですね. 
  背理法だったと思います. 

  **Robo**: はい, ですが`push_neg`と`intro f`から始めるのが良いでしょう. "
  push_neg
  intro f
  by_contra hf
  Hint "**カントール**: さて, どう思いますか？おそらく`f`によってカバーされない集合があるのではないでしょうか？"
  Hint (hidden := true) "**Robo**: 先ほどの集合を試してみてください！
  まず`let s := \{ a | a ∉ {f} a }`で導入できます. "
  let s := { a | a ∉ f a }
  Hint "**Robo**: 素晴らしい！
  これで例えば`specialize {hf} {s}`と続けられます. 
  後で`simp`を使うときは`simp [{s}]`とすれば, `simp`が定義を見通してくれます. "
  specialize hf s
  Hint "カントールは片足からもう片足へと飛び跳ねています. "
  obtain ⟨a, ha⟩ := hf
  Hint "**カントール**: そうだ！

  **あなた**: Robo, 今こそ先ほどの結果を使えるのでは？

  **Robo**: すみません, 全てが早すぎました！保存するのを忘れたようです. "
  by_cases h : a ∈ f a
  · suffices hn : a ∉ f a
    · contradiction
    rw [ha] at h
    simp[s] at h
    assumption
  · apply h
    rw [ha]
    simp[s]
    assumption
