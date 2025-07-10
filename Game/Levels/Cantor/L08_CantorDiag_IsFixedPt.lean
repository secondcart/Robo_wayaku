import Game.Metadata
import Game.Levels.Cantor.L07_idempotent

World "Cantor"
Level 8

Title ""

Introduction
"
カントールは着地し, 自転車から降り, 再び舞台の端に来て手を擦り合わせる. 

**カントール**: 君たちは今, 核心に近づいている! 
よく見れば, 君たちの目の前には
積集合 `A × A` 上で定義された写像がある! 
そして積集合には対角線がある! 
"

Conclusion
"
  **カントール**: とても素晴らしい! 

  彼は拍手する. 

  **あなた**: ええと, 今は何も理解できなくなってしまいました. 
"

open Function Set

Statement {A Y : Type} {f : A → A → Y} {s : Y → Y}
     {a : A} (ha : f a = fun a' ↦ s (f a' a')) :
    IsFixedPt s (f a a) := by
  Hint "
    **あなた** *(Roboに向かって)*: ここに積集合が見える? 

    **Robo**: ああ, もちろん. `f`の括弧の位置を思い出して: `A → (A → Y)`. 
    `A`から`A → Y`への写像の集合への写像は, 
    `A × A`から`Y`への写像と同じだよ. 

    あなたは眉をひそめる. 

    **Robo**: いやいや, これはエポで既に考えたことだよ! 
    `{f} {a} {a}`は, `{f} {a}`を`{a}`に適用したものと解釈できるし, 
    `{f}`を`({a},{a})`に適用したものとも解釈できる. 

    **カントール**: その通り! そして要素`({a},{a})`は対角線上にある! 

    **Robo**: 一方, 仮定`{ha}`は, 
    `f`を`A → (A → Y)`として解釈する方が自然な形で書かれている. 
    "
  unfold IsFixedPt
  Branch
    rw [ha]
    Hint "**Robo**:
      今, 君は基本的に`f a a`の両方を`s f a a`で置き換えた. 
      これでは堂々巡りだ. おそらく証明目標の2番目の`f a a`だけを
      書き換えたいのだろう. それは`nth_rw 2 [{ha}]`でできる. 
    "
    simp
  Branch
    nth_rw 2 [ha]
  apply congr_fun at ha
  specialize ha a
  rw [← ha]


TheoremTab "Function"
