import Game.Metadata

World "Logo"
Level 5

Title "True or False" -- "True or False"

Introduction
"
次に来た家臣は悪戯好きだ.
"

Statement : True := by
  Hint "
    **Robo** この`True`は特別な命題で, 常に無条件に真となる命題です.

    **あなた** では, 具体的に何を証明すればいいのですか?

    **Robo** おそらく何もありません. `decide`を試してみてください. "
  decide

Conclusion
"
**悪戯好き** あなたがまともな方かどうか確かめたかっただけです…

**あなた** *(Roboに向かって)* この`decide`をいつも使えないのですか?

**Robo** いいえ, `decide`は特別な状況, つまり命題が真かどうかを決定する簡単なアルゴリズムがある場合にのみ機能します.

# 今回学んだこと

## Tactics
### decide
- `decide`は単純なアルゴリズムで決定可能な命題を証明します. 例えば：
  - `Even 4`
  - `2 ≤ 5`
  - `4 ≠ 6`
  - `Prime 7`

## Definitions
### False
- `False : Prop` は常に偽な命題.

### True
- `True : Prop` は常に真な命題.
"

NewDefinition True False
NewTactic decide
DisabledTactic tauto
