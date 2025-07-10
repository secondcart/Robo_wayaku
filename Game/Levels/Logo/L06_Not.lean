import Game.Metadata

World "Logo"
Level 6

Title "Not"

Introduction
"
悪戯っ子にはもう一人姉妹がいるようだ。
"

Statement : ¬False := by
  Hint "
    **ロボ**: この記号`¬`は否定を意味します。つまり命題`(A : Prop)`が
    真ならば、`¬A`は偽となり、その逆もまた然りです。

    **あなた**: そして`False`はおそらく常に偽となる命題なのですか？

    **ロボ**: はい、その通りです。

    **あなた**: これは結局`decide`ではないのですか？

    **ロボ**: 試してみてください！"
  decide

Conclusion
"
姉妹は笑いながら兄の後を追いかけていった。
"

NewDefinition False Not
DisabledTactic tauto
