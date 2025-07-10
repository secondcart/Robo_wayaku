import Game.Metadata
import Game.Levels.Cantor.L09_CantorDiag

World "Cantor"
Level 10

Title ""

Introduction
"
**カントール**: さあ, この美しい対角線論法を使って, `A → Set A`の全射写像が存在しないことをもう一度示してみよう! 
`Set A`を`A → Prop`と解釈するだけだ! 

**あなた**: え? 

**Robo**: 部分集合`S : Set A`は, `a : A`を`a ∈ S`という命題に写す`A → Prop`の写像と同一視できます. 
形式主義者にとっては同じものです. 
"
Conclusion "
  **あなた**: これが本当に簡単だったのかどうかわかりません…
"

open Set Function

Statement {A : Type} : ¬ ∃ f : A → Set A, Surjective f := by
  Branch -- (This branch is not really needed, as it ends up with the same proof state as main branch.)
    by_contra h
    obtain ⟨f, hf⟩ := h
    Hint (hidden := true) "
    **あなた**: ここで`cantor_diagonal`を使うの? 

    **Robo**: おそらくね, 例えば`apply cantor_diagonal at {hf}`とかで. 
    "
  push_neg
  intro f
  by_contra hf
  Hint (hidden := true) "
    **あなた**: ここで`cantor_diagonal`を使うの? 

    **Robo**: おそらくね, 例えば`apply cantor_diagonal at {hf}`とかで. 
  "
  Branch
    clear hf
    let _C := { a | a ∉ f a }
    Hint "**カントール**: いやいや! 私の美しい定理`cantor_diagonal`を使うんだよ! "
  Branch
    specialize hf { a | a ∉ f a }
    Hint "**カントール**: いやいや! 私の美しい定理`cantor_diagonal`を使うんだよ! "
  apply cantor_diagonal at hf  -- L09
  -- now see L05
  Hint (hidden := true) (strict := true) "
  **カントール**: `¬ .`には不動点がないことはもう考えたんじゃないのかい? "
  specialize hf (¬ .) -- or specialize h Not -- or specializa h (fun A ↦ ¬ A)
  obtain ⟨a, hA⟩ := hf
  unfold fixedPoints IsFixedPt at hA
  simp at hA

  DisabledTactic by_cases
