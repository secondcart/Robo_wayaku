import Game.Metadata

open Nat

World "Luna"
Level 6

Title ""

Introduction
"**Ritha** 私もやってみていい? ほら. "

open Finset
namespace Robo.ZZ.Finset

/-- (version for ℤ)-/
TheoremDoc Robo.ZZ.Finset.insert_Icc_eq_Icc_add_one_right as "insert_Icc_eq_Icc_add_one_right" in "≤"

Statement insert_Icc_eq_Icc_add_one_right {a b : ℤ} (h : a ≤ b + 1) :
  insert (b + 1) (Icc a b) = Icc a (b + 1) := by
  Hint "
    **あなた** Iccって何?

    **Ritha** 左閉右閉の**閉**区間よ.

    **Robo** ℕでは`Icc a b`を[a, b]や$\\\{a, a+1,\\dots,b\\}$と書くでしょう.
    示すべきは：
     $$
     [a, b] ∪ \\\{ b + 1 \\} = [a, b + 1]
     $$
     "
  Hint (hidden := true) "**Robo** 集合の等式は`ext`で. "
  ext x
  Hint "
    **Robo** すぐに`simp`も使いましょう.
  "
  simp
  Hint "Rithaがまた何か書いている. "
  omega


TheoremTab "≤"

/-- (version for ℕ)-/
TheoremDoc Robo.NN.Finset.insert_Icc_eq_Icc_add_one_right as "insert_Icc_eq_Icc_add_one_right" in "≤"
-- /-- (version for ℤ)-/  -- see above
-- TheoremDoc Robo.ZZ.Finset.insert_Icc_eq_Icc_add_one_right as "Robo.NN.Finset.insert_Icc_eq_Icc_add_one_right" in "≤"
/-- (version for ℕ)-/
TheoremDoc Robo.NN.Finset.insert_Icc_eq_Icc_sub_one_left as "insert_Icc_eq_Icc_sub_one_left" in "≤"
/-- (version for ℤ)-/
TheoremDoc Robo.ZZ.Finset.insert_Icc_eq_Icc_sub_one_left as "insert_Icc_eq_Icc_sub_one_left" in "≤"
/-- (version for ℕ)-/
TheoremDoc Robo.NN.Finset.insert_Icc_add_one_left_eq_Icc as "insert_Icc_add_one_left_eq_Icc" in "≤"
/-- (version for ℤ)-/
TheoremDoc Robo.ZZ.Finset.insert_Icc_add_one_left_eq_Icc as "insert_Icc_add_one_left_eq_Icc" in "≤"
/-- (version for ℕ)-/
TheoremDoc Robo.NN.Finset.insert_Icc_sub_one_right_eq_Icc as "insert_Icc_sub_one_right_eq_Icc" in "≤"
/-- (version for ℤ)-/
TheoremDoc Robo.ZZ.Finset.insert_Icc_sub_one_right_eq_Icc as "insert_Icc_sub_one_right_eq_Icc" in "≤"

NewTheorem
Robo.NN.Finset.insert_Icc_eq_Icc_add_one_right
Robo.NN.Finset.insert_Icc_eq_Icc_sub_one_left
Robo.ZZ.Finset.insert_Icc_eq_Icc_sub_one_left
Robo.NN.Finset.insert_Icc_add_one_left_eq_Icc
Robo.ZZ.Finset.insert_Icc_add_one_left_eq_Icc
Robo.ZZ.Finset.insert_Icc_add_one_left_eq_Icc
Robo.NN.Finset.insert_Icc_sub_one_right_eq_Icc
Robo.ZZ.Finset.insert_Icc_sub_one_right_eq_Icc

Conclusion ""
