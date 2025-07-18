import Game.Metadata

World "Logo"
Level 7

Title "矛盾からはなんでも導ける"

Introduction
"
次に3人の曲者がやってきます. 最初の者は次の問題を抱えています.
"

Statement (A : Prop) (h : False) : A := by
  Hint "**あなた** これを正しく読むと, `{A}`は命題で,
    さらに`{h}`という仮定があります. それは…

    **Robo** …`False`が成り立つと言っています.

    **あなた** `False`は決して成り立たないんじゃないですか?

    **Robo** はい, その通りです. この仮定は`False`, つまり偽です.
    偽の仮定からは, どんなことでも証明できるのはご存知でしょう!
    特に求められている命題`{A}`もです.

    **あなた** で, どうやってこのFormalosophに説明すればいいの?

    **Robo** 一般的に成り立つ仮定`True`と彼の仮定`False`の間に矛盾があることを指摘する必要があると思います. `contradiction`を試してみてください. "
  contradiction

Conclusion
"
最初の曲者はどうやら満足したようです.

**あなた** これは背理法だったの?

**Robo** いえいえ, 背理法はもっと違うものです. ここでの論点は, 仮定の中に`contradiction`があるので, どんな命題でも導かれるということです.
"

NewTactic contradiction
DisabledTactic tauto
