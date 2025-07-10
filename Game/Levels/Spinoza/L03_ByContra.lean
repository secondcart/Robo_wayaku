import Game.Metadata

World "Spinoza"
Level 3

Title "Widerspruch"

Introduction "**ベネディクトゥス**: ここに別のバリエーションがあります. "

Statement (A B : Prop) (g : A → B) (b : ¬ B) : ¬ A := by
  Hint "
    **Robo**: ゴールにある`¬`は, しばしば矛盾による証明を行いたいことを意味します. 

    **あなた**: どうやってやるの? `contradiction`を使う? 

    **Robo**: `by_contra h`で矛盾による証明を開始します. `contradiction`で終了します. "
  by_contra h
  Hint "
    **Robo**: 今, あなたは仮定`{h} : {A}`を持っています. これを使って矛盾を導く必要があります. 

    例えば, `suffices`を使って導きたい矛盾を指定できます. `suffices k : B`のように. "
  suffices k : B
  Hint "
    **あなた**: ああ, 今は単に仮定`{B}`と`¬{B}`が矛盾していると言えますね. "
  contradiction
  Hint "
    **Robo**: そして今, この矛盾に至る中間結果を導く必要があります. "
  apply g
  assumption

Conclusion "**ベネディクトゥス**: あなたの上達が早いのがわかります！"


NewTactic by_contra
