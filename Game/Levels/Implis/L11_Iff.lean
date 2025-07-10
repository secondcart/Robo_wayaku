import Game.Metadata

World "Implis"
Level 11

Title "Genau dann wenn"

Introduction
"
**作戦責任者**: ああ, 次のページもこの同僚のものだ. 
しかし, ここにメモが付いている. 以前この問題の証明をしたことがあるが, 
彼は気に入らなかった. `rw`も`apply`も使わない証明を望んでいたんだ!!

彼は深く息を吸い, ため息をつく. 

**作戦責任者**: 彼はいつも自分を実際よりずっと愚かだと装っていると思う. 
でも, 君ならできると思うかい？
"

Statement (A B : Prop) : (A ↔ B) → (A → B) := by
  Hint "**あなた**: うーん, 少なくとも含意の部分から始められるかな. "
  Hint (hidden := true) "**Robo**: そうだね, それは`intro`だった. "
  intro h
  Hint "
    **あなた**: えーと, `rw [{h}]`や`apply ({h}.mp)`は知ってるけど, 今回はそれを避けたいんだよね. 

    **Robo**: できることは, `obtain ⟨mp, mpr⟩ := {h}`を使って仮定を2つに分けることだよ. "
  Branch
    intro
    Hint "
        **Robo**: ここでは`rw [←{h}]`か`apply {h}.mp`を使う必要がある. 
      一歩戻って, Goalが`A → B`になるようにした方がいいよ. "
  obtain ⟨mp, _mpr⟩ := h
  Hint (hidden := true) "**あなた**: ああ, これで証明目標が仮定の中にあるんだ. "
  assumption

Conclusion
"
**作戦責任者**: 完璧, これで十分だ！
"

OnlyTactic intro obtain assumption
DisabledTactic rw apply tauto
