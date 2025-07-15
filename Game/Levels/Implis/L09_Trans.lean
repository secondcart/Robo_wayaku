import Game.Metadata

World "Implis"
Level 9

Title "であるとき, かつそのときに限り4"

Introduction
"
**あなた** どうもこの`rw`は, 回りくどく議論しているような気がするんだ. まっすぐに進む方法はないのか, それともここにいるみんなはひねくれているのか?

**Robo** たぶん`trans`の方がいいと思うよ. これを使えば, $B \\iff A \\iff D \\iff C$という同値の連鎖を一歩ずつ進められる：まず`trans A`で`B \\iff A`の中間ステップを導入し, 次に`trans D`で次のステップに進むんだ.
"

Statement (A B C D : Prop) (h₁ : C ↔ D) (h₂ : A ↔ B) (h₃ : A ↔ D) : B ↔ C := by
  trans A
  symm
  assumption
  trans D
  assumption
  symm
  assumption
Conclusion
"
**Robo** どうだい, こっちの方が良かった?

**あなた** わからない. とにかく先に進めるよ.

# 今回学んだこと
## Tactics
### trans
- `trans`は等式または同値に中間ステップを挿入します:

| 変更前          | 変更後                  |
|:------------|:-------------------|
| `⊢ A = C`   | `⊢ A = B`と`⊢ B = C`|
| `⊢ A ↔ C`   | `⊢ A ↔ B`と`⊢ B ↔ C`|
"

NewTactic trans

DisabledTactic tauto rw nth_rw
