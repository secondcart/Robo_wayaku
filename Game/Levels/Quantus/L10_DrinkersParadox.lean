import Game.Metadata

World "Quantus"
Level 10

Title "酒飲みのパラドックス"

Introduction
"
**あなた** あなたたちはいつも合唱で話すか, バラバラに話すことしかできないの?

再び長い沈黙が続く. そして突然

**全員** 私たちの中には一人, その人が話すと全員が話し出す人物がいる!

あなたは頭を掻く.

**Robo** 当然だよ. これは有人惑星ならどこでも同じさ!

**あなた** え?

**Robo** これは「酒飲みのパラドックス」のバージョンだよ! 知らないの? なら手元のライブラリで調べてみたら! *どのバーにも, その人が飲むと全員が飲むという性質を持つ人物がいる*. 正確には：空でないバーならね.

**あなた** 信じられない.

**Robo** 私は信じるよ. むしろ, 君が証明できるとさえ思ってる. ほら, 試してみて!
"

Statement {People : Type} [h_nonempty : Nonempty People] (isDrinking : People → Prop) :
    ∃ (x : People), isDrinking x → ∀ (y : People), isDrinking y := by
  Hint "
    **あなた** つまり, `{isDrinking}`はまた述語ってこと…
    `p`が人物なら, `{isDrinking} p`は真か偽の命題だ.
    まあそうだよね.
    "
  Hint (hidden := true) "
    **あなた** で, どう始めれば?

    **Robo** 言った通り, 手元のライブラリを見るのが一番だよ.
    正しければ, 場合分けが役立つと思う. `∀ (y : {People}), {isDrinking} y`が真か偽かでね.
    "
  Hint (hidden := true) "**Robo** `by_cases`を見てみて. "
  by_cases h : ∀ y, isDrinking y
  · Hint (hidden := true) "
      **あなた** で, 誰を選べば?

      **Robo** 関係ないんじゃない? 仮定`h_nonempty`から誰かいることはわかってる. "
    obtain ⟨someone⟩ := h_nonempty
    use someone
    intro
    assumption
  · Hint (hidden := true) "**Robo** ここは`push_neg at {h}`で進められるよ. "
    push_neg at h
    Hint (hidden := true) "**あなた** つまり`{h}`の後, 飲まない人物が存在する. これを使って命題を自明に真にできる?

    **Robo** 仮定`{h}`に`obtain`をどう適用するか見てみて. "
    choose p hp using h
    use p
    intro hp'
    Hint (hidden := true) "**Robo** `{hp}`と`{hp'}`を見て何がわかる? "
    contradiction



TheoremTab "Logic"

Conclusion
"
**あなた** わかった. でももうこの述語論理にはうんざりだ!

**Robo** なら早く出発しよう! でも聞く前に――この惑星で学んだことのまとめだ:


|               | 説明                         |
|:--------------|:-----------------------------|
| `∃`           | 存在量化子                   |
| `∀`           | 全称量化子                   |
| `Even n`      | `n`は偶数                    |
| `Odd n`       | `n`は奇数                    |

|       | タクティック                  | 例                                                     |
|:------|:------------------------------|:-------------------------------------------------------|
| *13ᶜ* | `rw`                          | 等式で書き換え.                                        |
| 15    | `ring`                        | `+, -, *, ^`を含む方程式を解く.                        |
| *4ᵇ*  | `decide`                      | 具体的な数値に関する命題も答えられる.                  |
| 16    | `unfold`                      | 定義を視覚的に展開する.                                |
| 17    | `use`                         | Goal中の`∃`に対して具体例を与える.                     |
| 18    | `choose x hx using h`         | 仮定中の`∃`を分解する.                                 |
| *8ᵇ*  | `intro`                       | Goal中の`∀`に対処する.                                 |
| 19    | `push_neg`                    | Goal中の`¬∃`や`¬∀`に対して使用.                        |
"
