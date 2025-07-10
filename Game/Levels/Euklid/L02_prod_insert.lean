import Game.Metadata

World "Euklid"
Level 2
Title ""

Introduction "廊下を少し進むと, また地面に開いた本が見えます. "

open Finset
namespace Nat

Statement (p : ℕ) (hp : Prime p) (A : Finset ℕ): (∃ a ∈ A, p ∣ a) → p ∣ ∏ a ∈ A, a := by
  Hint "**Robo**: この行も非常に理にかなっています:
  素因数が積の因数`a`を割り切るなら, 確かに積全体も割り切れます. 

  **あなた**: しかし最初の「証明行」でさえ, 生きているとは言えません. 

  **Robo**: いいえ, 違います. でも自分で試してみましょう. 
  もちろん`intro`から始めます. 
  "
  intro h
  Hint "**Robo**: そして今, 仮定`{h}`を3つの構成要素に分解します. "
  obtain ⟨a, ha, hpa⟩ := h
  Hint "
    **あなた**: おそらく, 因数`{a}`を何とかして積から分離したいのでしょうか? 

    **Robo**: はい, それが役立つはずです. `insert_erase`のようなものが必要だと思います. 
  "
  Hint (hidden := true) "
    **Robo**: `rw [← insert_erase {ha}]`を試してみてください. 
  "
  rw [← insert_erase ha]
  Hint "
    **Robo**: そして今, `prod_insert`を使用して, 実際に因数を取り出します. 
  "
  rw [prod_insert]
  Hint (hidden := true) "
    **Robo**: 残りは簡単なはずです. `Prime.dvd_mul`は既に証明済みです. 
  "
  · rw [Prime.dvd_mul]
    · left
      assumption
    · assumption
  · simp

/---/
TheoremDoc Finset.prod_insert as "prod_insert" in "∑ Π"

NewTheorem Finset.prod_insert
