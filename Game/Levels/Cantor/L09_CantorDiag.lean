import Game.Metadata
import Game.Levels.Cantor.L08_CantorDiag_IsFixedPt

World "Cantor"
Level 9

Title ""

Introduction
"
**Cantor**: 幸運を祈る! 
"

Conclusion "**あなた**: さて, この一般的な形式で元の問題を再度解決したいと思います. "

open Function Set

/---/
TheoremDoc cantor_diagonal as "cantor_diagonal" in "Function"

Introduction "
  **Cantor**: 注意してください! すべてが明らかになります. これが鍵です! 
  先ほどの主張を少し言い換える必要があります. 

  彼は新しいメモをあなたに投げます. 
"

Conclusion "
  **Cantor**: 素晴らしい! 
"

Statement cantor_diagonal {A Y : Type} (f : A → A → Y) (hf : Surjective f) :
    ∀ s : Y → Y, Nonempty (fixedPoints s) := by
  Hint "
    **あなた**: 特定の仮定の下で, *任意の*自己写像`s : {Y} → {Y}`が
    不動点を持つことを示す必要がありますか? すべての集合上に不動点のない
    自己写像が存在しないのでしょうか? 
    例えば, $ℕ$や$ℝ$上の$n ↦ n + 1$など...

    **Robo**: ...または$\\\{0,1\\}$上の非自明な置換? 

    彼もどうやら少し混乱しているようです. 

    **Robo**: つまり, `Y`が一点集合でない限り, 
    常に不動点を持たない自己写像が存在するはずです. 

    **Cantor**: まあ, それがまさに面白いところです! 待っててください! 
    "
  intro s
  Hint (hidden := true) "**Cantor**: もちろん, `{f}`の全射性を
  何らかの形で利用する必要があります. しかし, 先ほどすでに, 
  どの写像`{A} → {Y}`の原像を考えればいいか教えましたね...

  **Robo** *(あなたに向かって)*: うーん...彼の言っていることがわかりますか? 
  もちろん, 次のような写像を定義できます:
  ```
  let c : {A} → {Y} := fun a ↦ _
  ```
  そしてこの写像`c`の原像を考えます. 
  しかし, 私は今少し迷子になっています. 
  "
  let c : A → Y := fun (a : A) ↦ s (f a a)
  Hint "**Cantor**: 良い選択です! "
  obtain ⟨a, ha⟩ := hf c
  use (f a a)
  unfold fixedPoints IsFixedPt
  simp
  apply congr_fun at ha
  specialize ha a
  --simp [c] at ha  -- optional
  symm
  assumption

TheoremTab "Function"
