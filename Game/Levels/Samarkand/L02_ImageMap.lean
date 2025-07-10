import Game.Levels.Samarkand.L01_ImagePreimage

open Set

World "Samarkand"
Level 2
Title "Bild/Urbild"

Introduction "アラプカがもう一つ課題を出しています。"

Statement {A B C : Type} (f : A → B) (g : B → C) : image (g ∘ f) = (image g) ∘ (image f) := by
  Hint "
    **あなた**: ああ！つまり, この''のような煩わしい記法が嫌なら, 単に`image`と書いてもいいんだ？

    **ロボ**: いいえ, よく見てください。ここでの`image f`は写像です。
    これはもちろん, Aの部分集合をBの対応する像集合に送る写像で, 
    ```
    image f = fun S ↦ f '' S
    ```
    つまり`image f`は`f ''`で表現できますが, 逆はできません。
  "
/-
This is literally true:
example : image f = fun S ↦ f '' S := by
  rfl
--/
  Hint (hidden := true) "
    **ロボ**: 2つの写像の一致を示す必要があります。`funext`を覚えていますか？
  "
  Branch
    funext
    Hint "
      **ロボ**: ああ, いや。これは複雑すぎます。明示的に`funext S`と書いた方がいいです。
      "
  funext S
  Hint (hidden := true) "
    **ロボ**: 今度は2つの集合の等価性を示す必要があります - `ext`が魔法の言葉です。
    "
  ext c
  Hint (hidden := true) "
    **ロボ**: これはきっと簡単に簡略化できるでしょう…
  "
  simp

NewDefinition Set.image Set.preimage

Conclusion "
  **アラプカ**: 素敵, 素敵。
"
