import Game.Metadata

World "Logo"
Level 6

Title "Not"

Introduction
"
悪戯好きな家臣には妹がいるようだ.
"

Statement : ¬False := by
  Hint "
    **Robo** この記号`¬`は否定を意味します. つまり命題`(A : Prop)`が
    真ならば, `¬A`は偽となり, その逆もまた然りです.

    **あなた** そして`False`はおそらく常に偽となる命題なのですか?

    **Robo** はい, その通りです.

    **あなた** これは結局`decide`ではないのですか?

    **Robo** 試してみてください! "
  decide

Conclusion
"
妹は笑いながら兄の後を追いかけていった.
"

NewDefinition False Not
DisabledTactic tauto
