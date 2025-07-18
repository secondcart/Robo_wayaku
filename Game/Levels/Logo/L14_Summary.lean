import Game.Metadata

World "Logo"
Level 14

Title "まとめ"

Introduction
"
ここで, この状況で最も重要な4つの戦術をもう一度示しておきます.

| (概要) | AND (`∧`)               | OR (`∨`)               |
|:------------|:-------------------------|:------------------------|
| 前提     | `obtain ⟨h₁, h₂⟩ := {h}`   | `obtain h \\| h := {h}`   |
| 目標        | `constructor`            | `left`/`right`

最後の家臣が前に出てきます. 彼女の訴えはこれまでのものより少し複雑です.

**Robo** 学んだことをすべて使ってみてください.       |
"

-- Note: The other direction would need arguing by cases.

Statement (A B C : Prop) (h : A ∨ (B ∧ C)) : (A ∨ B) ∧ (A ∨ C) := by
  Hint (hidden := true)
    "**Robo**: まず前提 {h} を `obtain ⟨⟩ := {h}` で分割するといいよ"
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
  Hint (hidden := true) "**Robo**: これでゴールの `∧` を `constructor` で処理できるよ"
  · constructor
    · left
      assumption
    · left
      assumption
  · Hint (hidden := true)
      "**Robo**: ここで前提 {h} をもう一度 `obtain` で分割するといいかも"
    Branch
      constructor
      · Hint "**Robo**: この順序の欠点は, 各Subゴールで `obtain ⟨⟩ := h` を呼ぶ必要があることだね"
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
**Robo** ブラボー! さあ, 新しい列ができる前にここを離れよう!

*Logisinde* 女王はその間に眠りにつき, あなたたちはこっそりと逃げ出します.
"

DisabledTactic tauto
