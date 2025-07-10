import Game.Metadata

World "Logo"
Level 5

Title "True or False" -- "True or False"

Introduction
"
次の順番の家臣は悪戯好きだ。
"

Statement : True := by
  Hint "
    **ロボ**: この`True`は特別な命題で、常に無条件に真となる命題です。

    **あなた**: では、具体的に何を証明すればいいのですか？

    **ロボ**: おそらく何もありません。`decide`を試してみてください。"
  decide

Conclusion
"
**悪戯好き**: あなたがまともな方かどうか確かめたかっただけです…

**あなた** *(ロボに向かって)*: この`decide`をいつも使えないのですか？

**ロボ**: いいえ、`decide`は特別な状況、つまり命題が真かどうかを決定する簡単なアルゴリズムがある場合にのみ機能します。
"

NewDefinition True False
NewTactic decide
DisabledTactic tauto
