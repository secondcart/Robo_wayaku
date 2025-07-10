import Game.Metadata

World "Piazza"
Level 4

Title ""

Introduction
"
  **Sub:** 私もすでにいくつか学びました:
"
namespace Set

#check  (univ : Set ℕ)

Statement : { n : ℕ | Even n} ∪ { n : ℕ | Odd n} = univ := by
  Hint "
    **Du**:  `univ`って何ですか? 

    **Robo**:  `univ`は最大部分集合です：すべての自然数を含みます. 

    **Du**:  つまり単に`ℕ`ですか? 

    **Robo**:  はい, でも違います. `univ : Set ℕ`は「ℕ全体」ですが, ℕの部分集合として扱われます. 

    Ext, Fin, Set, Sub, Memがあなたを見つめています. 

    **Set**:  これは混同するはずがないでしょう！ここにブルーベリーがあります, 
    これは全てのブルーベリーが入ったかごで, このベリーはかごの中にあります. 

    **Mem**:  同様に, 5は自然数です(`5 : ℕ`), 
    `univ : Set ℕ`は全ての自然数の集合で, `5`はこの集合に含まれます(`5 ∈ univ`). 
    何が混乱するのでしょうか? 

    **Robo** (*あなたに*): 頭を悩ませないでください. 
    ここではまず`rw [eq_univ_iff_forall]`から始めることをお勧めします, 
    そうすれば求められていることが明確にわかります. 
    "
  /-
  `ext` also works, but WANT to introduce
  `eq_univ_iff_forall` and `generalize` here!
  So `ext` is disabled
  -/
  /-
  Branch
    ext
    simp
  -/
  rw [eq_univ_iff_forall]
  Hint "
    **Robo**: そして今度は`simp`です. 最初から`simp [eq_univ_iff_forall]`とすることもできました. 
    "
  simp
  intro x
  Hint "
    **Du**: 次は`by_cases h : Even n`ですか? 

    **Robo**: はい, それでゴールに到達できます. 
    しかし実際には`Even x ∨ ¬Even x`はトートロジーです. 
    `tauto`に認識させるためには, 適切に抽象化する必要があります. 
    ここでは例えば以下のようにできます:
    ```
    generalize h : (Even x) = A
    ```
    "
  /-Branch
    by_cases h : Even n
    left
    assumption
    right
    assumption
  -/
  generalize h : (Even x) = A
  tauto

TheoremTab "Set"

NewTactic generalize
DisabledTactic ext

/---/
TheoremDoc Set.eq_univ_iff_forall as "eq_univ_iff_forall" in "Set"
NewTheorem Set.eq_univ_iff_forall

NewDefinition Set.univ

Conclusion ""
