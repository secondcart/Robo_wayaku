import Game.Metadata

World "Euklid"
Level 3
Title ""

Introduction "
  次の開いた本を見つけるには, かなり歩かなければなりません。
  ロボは, 帰り道がわかるように赤い糸を巻き始めました。
"

open Finset
namespace Nat

Statement (hf : Set.Finite { p : ℕ | Prime p}) : ∃ (a : ℕ), a > 0 ∧ ∀ (p : ℕ), Prime p → p ∣ a := by
  -- tauto -- If we don't insist a > 0, tauto solves this!
  Hint "**ロボ**: おお！これは面白そうですね：
  素数が有限個しかないと仮定すると, 
  すべての素数で割り切れる正の自然数が存在することになります。

  **あなた**: はい, 少しばかげているように聞こえますが正しいです。証明は？最初の行に
  `let all_primes := hf.toFinset`とあります。これは何か意味がありますか？

  **ロボ**: 非常に意味があります！
  この主張を示すためには, すべての素数の積を考える必要があります。
  そしてこれを構文的に可能にするためには, すべての素数の集合を
  `Finset`として扱う必要があります。最初の行はまさにそれを行います：仮定`hf`を使って
  `\{ p : ℕ | Prime p} : Set ℕ`から有限部分集合`\{ p : ℕ | Prime p} : Finset ℕ`
  を作ります。

  **あなた**: わかりました, 試してみます。
  "
  let all_primes := hf.toFinset
  Hint "
    **あなた**: 次の行は？

    `all_primes.bubblewrap = blister cong foo`

    これも意味がありますか？

    **ロボ**: いいえ, これはまた非常にナンセンスです。
  先ほど言ったように, これらの数の積を使いたいでしょう。
  積記号は`\\prod`と書きます。"
  use ∏ p ∈ all_primes, p
  Hint "
    **ロボ**: ブラボー。

    **あなた**: 今非常に役立ついくつかのことを以前示したのでは？

    **ロボ**: おっと。はい, しましたが, 残念ながら保存していませんでした。
  議論がどのように進んだかをもう一度再構築する必要があります。
    "
  constructor
  · Hint "**ロボ**: ここでは`Finset.prod_pos`が再び役立つでしょう。"
    apply Finset.prod_pos
    intro p
    simp [all_primes]
    intro h
    rw [prime_def] at h
    linarith
  · intro p hp
    -- previous lemma would be useful now, but want to practise!
    have hp' : p ∈ all_primes := by
      Hint (hidden := true) "
        **ロボ**: ここで`simp`が機能しない場合, `simp`に
        `all_primes`の定義を教える必要があるかもしれません。つまり`simp [all_primes]`です。
        "
      simp [all_primes]
      assumption
    rw [← insert_erase hp']
    rw [prod_insert]
    · use ∏ x ∈ all_primes.erase p, x
    · simp


/-- Ist eine Teilmenge `A : Set T` mit der Annahme `h : Set.Finite A` gegeben,
so ist `h.toFinset : Finset T` dieselbe Teilmenge `A`,
aber nun explizit als endliche Teilmenge aufgefasst. -/
TheoremDoc Set.Finite.toFinset as "toFinset" in "Set"

NewTheorem Set.Finite.toFinset
NewDefinition Set.Finite

Conclusion "
  床にいくつかの本が置かれている通路に入ります。
  しかしどれも開かれていません。
  次の交差点で, 再び床に本が置かれた別の通路が分かれています。

  **あなた**: これはたぶん手がかりですか？

  **ロボ**: それを追いましょう！
 "
