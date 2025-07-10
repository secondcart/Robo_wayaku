import Game.Metadata

World "Euklid"
Level 4
Title ""

Introduction "しばらくすると、紙をめくる音が聞こえてきました。
角を3回曲がると、あなたはオフィスにたどり着きます。
ドアには「ユークリッド、図書館長」と書かれています。

**ユークリッド**:
こんにちは！ 訪問者が来てくれるなんて嬉しいですね。
もしここが*どんな*図書館か知っていたら、
私は館長の職を受けなかったでしょう。

**あなた**: どんな図書館が理想だったのですか？

**ユークリッド**: ここには「特に」私の有名な祖先の著作の
Lean版があると約束されました。彼はちなみに*あなたの*宇宙から来たのです。
そして私は何年もカタログや本自体を探していますが、
ほんの小さな断片しか見つかりません。

見てください、私はついに自分で彼の結果の一つを
定式化し始めました。手伝ってくれませんか？"

open Finset
namespace Nat

Statement : ¬ Set.Finite { p : ℕ | Prime p} := by
  Hint "**ロボ**: もちろん、やりましょう。
  これは典型的な背理法の証明です:
  もし素数が有限個しかないなら、全ての素数の積に1を足した数は
  どの素数でも割り切れません。
  一方、`exists_prime_and_dvd`が成り立ちます。矛盾です。
  "
  by_contra hf
  -- notation to make equations human-readable:
  let all_primes := hf.toFinset
  let prod : ℕ := ∏ p ∈ all_primes, p
  let new_prime : ℕ := prod + 1
  -- As for any natural number > 1, there must be some prime that divides new_prime:
  have h_exists_prime_factor : ∃ p : ℕ, Prime p ∧ p ∣ new_prime := by
    have : 1 < new_prime := by
      have : 0 < prod  := by
        apply Finset.prod_pos
        intro p
        simp[all_primes]
        intro h
        rw [prime_def] at h
        linarith
      simp[new_prime]
      assumption
    apply exists_prime_and_dvd
    linarith
  -- On the other hand, by construction, no prime divides new_prime:
  have h_no_prime_divides : ∀ p : ℕ, Prime p →  ¬ p ∣ new_prime := by
    intro p hp
    let q := ∏ p' ∈ (all_primes.erase p), (p' : ℕ)
    -- new_prime = p * q + 1 …
    have h : prod = p * q := by
      /- slightly longer version that uses prod_insert: -/
      simp[prod]
      have : p ∈ all_primes := by
        simp[all_primes]
        assumption
      rw[← Finset.insert_erase this]
      apply Finset.prod_insert
      simp
      /- shorter, older version that used mul_prod_erase: -/
      /-
      symm
      apply Finset.mul_prod_erase all_primes id
      simp[all_primes]
      assumption
      -/
    simp[new_prime]
    rw [h]
    -- … so it cannot be divisible by p:
    apply not_dvd_of_between_consec_multiples (n := p) (k:=q) (m := p*q+1)
    · linarith
    · simp [prime_def] at hp
      linarith
  -- Now we have a contradiction:
  obtain ⟨p, hp, h_dvd⟩ := h_exists_prime_factor
  specialize h_no_prime_divides p hp
  contradiction

Conclusion "ユークリッドは興奮して円陣を組んで踊ります。
彼はあなたたちを行かせたくないようです。
あなたたちは連絡を取り合うことを約束します。"
