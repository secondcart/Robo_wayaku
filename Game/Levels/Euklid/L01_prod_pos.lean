import Game.Metadata

World "Euklid"
Level 1
Title ""

Introduction "マークされた場所には次のように書かれています："

open Finset
namespace Nat

Statement (A : Finset ℕ) (h : ∀ a ∈ A, Prime a) : 0 < (∏ a ∈ A, a) := by
  Hint "**あなた**: この行は実際に読めます. 
  `∏ a ∈ A, a` は確かにLeanでAのすべての数値の積を表しているのでしょうか? 

  **Robo**: はい! そして次の行も意味が通ります: `apply prod_pos`."
  apply prod_pos
  Hint "**Robo**: しかしその後は再び完全な無意味な内容です. 
  ただ, この主張自体は正しいと思います. さあ, 私たち自身で解決しましょう. "
  intro a ha
  specialize h a ha
  rw [prime_def] at h
  linarith

/---/
TheoremDoc Finset.prod_pos as "prod_pos" in "∑ Π"

NewTheorem Finset.prod_pos

NewDefinition Prod
