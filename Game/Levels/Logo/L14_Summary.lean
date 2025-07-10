import Game.Metadata


World "Logo"
Level 14

Title "Zusammenfassung"

Introduction
"
最後の臣民が前に出てきます。彼女の訴えはこれまでのものより少し複雑です。

**ロボ** 学んだことをすべて使ってみてください。
ここで、この状況で最も重要な4つの戦術をもう一度示しておきますね。

| (概要) | AND (`∧`)               | OR (`∨`)               |
|:------------|:-------------------------|:------------------------|
| 前提     | `obtain ⟨h₁, h₂⟩ := h`   | `obtain h \\| h := h`   |
| 目標        | `constructor`            | `left`/`right`          |
"

-- Note: The other direction would need arguing by cases.

Statement (A B C : Prop) (h : A ∨ (B ∧ C)) : (A ∨ B) ∧ (A ∨ C) := by
  Hint (hidden := true)
    "**ロボ**: まず前提 {h} を `obtain ⟨⟩ := {h}` で分割するといいよ"
  Branch
    constructor
    · obtain h' | h' := h
      · left
        assumption
      · obtain ⟨h₁, _h₂⟩ := h'
        right
        assumption
    · obtain h' | h' := h
      · left
        assumption
      · obtain ⟨_h₁, h₂⟩ := h'
        right
        assumption
  obtain h | h := h
  Hint (hidden := true) "**ロボ**: これでゴールの `∧` を `constructor` で処理できるよ"
  · constructor
    · left
      assumption
    · left
      assumption
  · Hint (hidden := true)
      "**ロボ**: ここで前提 {h} をもう一度 `obtain` で分割するといいかも"
    Branch
      constructor
      · Hint "**ロボ**: この順序の欠点は、各サブゴールで `obtain ⟨⟩ := h` を呼ぶ必要があることだね"
        Branch
          right
          obtain ⟨h₁, _h₂⟩ := h
          assumption
        obtain ⟨h₁, _h₂⟩ := h
        right
        assumption
      · Branch
          right
          obtain ⟨_h₁, h₂⟩ := h
          assumption
        obtain ⟨_h₁, h₂⟩ := h
        right
        assumption
    obtain ⟨h₁, h₂⟩ := h
    constructor
    · right
      assumption
    · right
      assumption

Conclusion
"
**ロボ** ブラボー！さあ、新しい列ができる前にここを離れよう！

女王 *ロジジンデ* はその間に眠りにつき、あなたたちはこっそりと逃げ出します。
"

DisabledTactic tauto
