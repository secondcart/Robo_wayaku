import Game.Metadata

World "Logo"
Level 4

Title "命題"

Introduction
"
3番目の家臣が次の問題を持ってやってきました.
"

Statement (A : Prop) (hA : A) : A := by
  Hint "
    **Robo** ここで`{A} : Prop`は再び, `{A}`が何らかの命題であることを意味します.
      そして`{hA}`は`{A}`が真であるという仮定の名前です.

    **あなた** そしてこの仮定の下で, 今`{A}`を証明する必要があるのですか?

    **Robo**: はい. どうすればいいか, もう自分でわかりますよね? "
  Hint (hidden := true) "**Robo**: 先ほどと全く同じです:
    証明すべき命題自体が仮定の中に含まれています.
    ですから, `assumption`が再び機能するでしょう. "
  Hint (hidden := true) "**Robo**: 以前と同じように, 証明される文自体が仮定の一つなのです.
  だから, `assumption`もまた機能する. "
  assumption

Conclusion "
**家臣**: あっという間でした. 素晴らしい! どうもありがとう.
"

DisabledTactic tauto
