import Game.Metadata

import Game.Levels.Logo
import Game.Levels.Implis
import Game.Levels.Quantus

import Game.Levels.Saturn
import Game.Levels.Spinoza
import Game.Levels.Luna
import Game.Levels.Babylon

import Game.Levels.Cantor
import Game.Levels.Robotswana

import Game.Levels.Ciao

import Game.Levels.Prado
import Game.Levels.Euklid

import Game.Levels.Vieta
import Game.Levels.Epo
import Game.Levels.Mono
import Game.Levels.Samarkand
import Game.Levels.Iso

import Game.Levels.Piazza

-- *uncomment the following line to get the incomplete planets.*
-- import Game.DevPlanets

Title "Robo(和訳)"
Introduction
"
# このサイトについて
こちらは, 以下のサイトを和訳したものです. (2025/07/11)
https://adam.math.hhu.de/#/g/hhu-adam/robo
ただし, そのままの訳だと, 長くなる箇所があり, 多少意訳している.

# ゲームオーバーそれともQED?
コンピュータ支援証明が「本物の」数学とどう違うか気になりますか? それならここがぴったりです! このゲームでは, 証明アシスタントLean 4と数学ライブラリmathlibの使い方を学べます. 例えば, 帰納法を使った総和公式の証明, 写像が全射であることと右逆元を持つことが同値であることの証明, 自然数の列が非可算無限であることの証明, 正方行列の空間におけるトレースの特徴付けなどを行います.

インターフェースは簡略化されていますが, エディターモードを有効にすると,
Leanの標準IDEであるVSCodeとほぼ同じ感覚で使えます. スマートフォンやタブレットでは,
デフォルトのタイプライターモードのままで, 画面キーボードの自動補完/修正機能をオフにするのがおすすめです.

旅を始めるには, 最初の惑星Logoをクリックしてください.

# ゲームの進行状況
進行状況はブラウザのサイトデータとしてローカルに保存されます. これを削除すると進行状況が失われます!
多くのブラウザではサイトデータとクッキーが一緒に削除されますが,
メニューから進行状況をダウンロードして手動で保存することもできます.

# ゲームルール
真剣にプレイしたい場合は「Rules: regular」を選択してください.
少し見て回りたいだけなら「Rules: relaxed」を選ぶと, 前のレベルをクリアしていなくてもどのレベルでもプレイできます.

背景情報とクレジットは, メニューの「Game Info」で確認できます.

# 最新情報

【2025年3月28日】Formaloversumに新惑星「Euklid」が登場! その他にも多数の改善が加えられました.
とくに「Babylon」「Cantor」「Saturn」の各惑星や, 戦術・定義のドキュメントが強化されています.
Babylonでは, 今後は ℕ や ℤ の区間での総和を扱い, `Fin n` は使われません.
Saturnのラストには, 多項式的な平方和公式が登場します.

【2025年3月18日】「Quantus」から新惑星「Saturn」が分離. Lunaはサイズアップし, Piazzaも全面的に再設計されました.

【2025年2月20日】写像に特化した惑星群「Vieta」「Mono」「Epo」「Iso」「Samarkand」が完成しました.

【2025年1月25日】お別れ用の惑星「Ciao」が追加されました.
"

Info
"
このゲームは, 以下のリポジトリを和訳したものである. (2025/07/09)
[Robo](https://github.com/hhu-adam/Robo)

ただし, 準拠した和訳ではない.
以下は, 元のGame Infoをそのまま載せている.
## Projekt ADAM

Dieses Lernspiel wurde im Rahmen des Projekts
[ADAM: Anticipating the Digital Age of Mathematics](https://hhu-adam.github.io/)
an der Heinrich-Heine-Universität Düsseldorf entwickelt,
finanziert durch das Programm *Freiraum 2022* der *Stiftung Innovation in der Hochschullehre*.

## Spielinhalt

**Spoiler Alert** Auf [Github](https://github.com/hhu-adam/Robo?tab=readme-ov-file#overview-over-existing-content) findest du eine Übersicht über den groben mathematischen Inhalt aller Planeten.

## Credits

* **Projektleitung:** Marcus Zibrowius, Immi Halupczok
* **Game Engine:** Jon Eugster, Alexander Bentkamp, Patrick Massot – siehe [lean4game](https://github.com/leanprover-community/lean4game?tab=readme-ov-file#credits)
* **Levels:** Jon Eugster, Marcus Zibrowius, Sina Hazratpour
* **Konzept & Handlung:** Marcus Zibrowius
* **Illustrationen:** [Dušan Pavlić](https://www.behance.net/dusanpavlic#)

## Kontakt

Das Spiel wird laufend überarbeitet.
Wir freuen uns sehr über Erfahrungsberichte, Anregungen und Kritik,
zum Beispiel per Email an
[Marcus Zibrowius](https://www.math.uni-duesseldorf.de/~zibrowius/).
Wenn du spezifische Änderungswünsche hast oder Fehler findest, kannst du auch gern einen Issue auf GitHub erstellen:

* zum Spielinhalt im [Robo repo](https://github.com/hhu-adam/Robo/issues)
* zum Spielserver im [lean4game repo](https://github.com/leanprover-community/lean4game/issues).
"

Conclusion
"QED"


/-! Information to be displayed on the servers landing page. -/
Languages "de"
CaptionShort "Erkunde ein fremdes Universum mit deinem Smart-Elf Robo!"
CaptionLong "Dieses Spiel illustriert Beweisführung mit Lean anhand verschiedener Themen aus der Eingangsphase des Bachelorstudiums Mathematik."
-- Prerequisites "" -- add this if your game depends on other games
CoverImage "images/Cover.png"


/-! If you need to add manual dependencies in your planet graph, you can do so here: -/
Dependency Quantus → Piazza -- because of `∀`
Dependency Prado → Mono     -- beclause of `∃!`
Dependency Mono → Iso       -- because of `Injective`

Dependency Robotswana → Ciao
Dependency Cantor → Ciao
Dependency Samarkand → Ciao
Dependency Iso → Ciao
Dependency Euklid → Ciao

-- set_option lean4game.showDependencyReasons true

/-! Build the game. Show's warnings if it found a problem with your game.

(need to open all namespaces with local definitions) -/
-- open BigOperators in
MakeGame
