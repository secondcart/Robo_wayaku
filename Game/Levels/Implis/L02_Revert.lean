import Game.Metadata

World "Implis"
Level 2

Title "Revert"

Introduction
"
作戦責任者がコンテナから紙の山を取り出します。

**作戦責任者**: ここには本当にたくさん溜まってしまいました。もしあなたが
もう少し手伝ってくれると本当に助かります。

彼はあなたに一番上の紙を渡します。
"

Statement (A B : Prop) (hA : A) (h : A → B) : B := by
  Hint "
    **作戦責任者**: これは同僚からのものです。

    **Robo**: あ, これはどこかで読んだことがあります。待って…そうだ！あの時, 
    私がWikipediaをクロールしていた時のことだ: `モーダスポネンスは古代ロジックで既に知られていた推論規則で, 多くの論理的…`

    **あなた**: Robo！求められているのは証明であって歴史的な論文じゃない！それともここで
    `mopo`とかそんなので進められると思ってるの？

    **Robo**: はい, いいえ, すみません。`mopo`はありません。代わりに`revert {hA}`を試してみてください。
    "
  revert hA
  Hint "
    **あなた**: なるほど。`revert`は基本的に`intro`の逆ですね。

    **Robo**: その通りです。`intro`は証明目標内の含意`{A} \\to {B}`から前提を取り出して仮定にします。`revert`は逆に仮定を取り出して含意の前提として証明目標の前に置きます。さあ, もう終わらせてください。
  "
  assumption

Conclusion "作戦責任者は喜んであなたの解答を受け取り, 電話に手を伸ばします。"

NewTactic revert
DisabledTactic tauto
