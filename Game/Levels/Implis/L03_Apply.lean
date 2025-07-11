import Game.Metadata

World "Implis"
Level 3

Title "Apply"

Introduction
"
残念ながら電話での会話はうまくいっていません. 彼はまた電話を切り, 首を振ります. 

**作業責任者**: 月の反対側にいる同僚は`revert`を理解していません. あるいは
少なくともそう装っています. 他にアイデアはありますか? 

彼はあなたの証明の下に線を引き, 取り消し線付きの~`revert`~を追加し, 
その紙を再度あなたの前に差し出します. 
"

Statement (A B : Prop) (h : A) (hAB : A → B) : B := by
  Hint "
    **Robo**: おそらく, 与えられた含意を適用する方がより洗練された方法だったでしょう. 
    `apply hAB at h`を試してみてください. "
  Branch
    apply hAB
    Hint "
      **Robo**: 私は`… at h`と言いました. しかし, 単に`apply hAB`だけでも機能するようです. 
      これで, `hAB`を証明目標`B`に適用し, あとは`A`を証明するだけです. 
    "
    assumption
  apply hAB at h
  Hint "**あなた**: はい, これも自然に感じます. "
  assumption

Conclusion "今度は電話での会話がうまくいっているようです. "

NewTactic apply
DisabledTactic revert tauto
