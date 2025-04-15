# Coq workshop
Материалы к воркшопам по Coq/Rocq

## Ссылки
* [Офиициальный сайт](https://rocq-prover.org/)
* [Инструкция по установке](https://rocq-prover.org/install)
* [jsCoq](https://jscoq.github.io/scratchpad.html) - здесь можно попробовать всё онлайн без установки
* [coq-merge-sort](https://github.com/anton0xf/coq-merge-sort) - материалы и слайды к моему предыдущему докладу

## О чём это
* Coq/Rocq - это язык программирования с зависимыми типами и [proof assistant](https://en.wikipedia.org/wiki/Proof_assistant) ([инструмент интерактивного доказательства теорем](https://ru.wikipedia.org/wiki/%D0%98%D0%BD%D1%81%D1%82%D1%80%D1%83%D0%BC%D0%B5%D0%BD%D1%82_%D0%B8%D0%BD%D1%82%D0%B5%D1%80%D0%B0%D0%BA%D1%82%D0%B8%D0%B2%D0%BD%D0%BE%D0%B3%D0%BE_%D0%B4%D0%BE%D0%BA%D0%B0%D0%B7%D0%B0%D1%82%D0%B5%D0%BB%D1%8C%D1%81%D1%82%D0%B2%D0%B0_%D1%82%D0%B5%D0%BE%D1%80%D0%B5%D0%BC)) с поддержкой тактик
* [Соответствие Карри-Ховарда](https://en.wikipedia.org/wiki/Curry%E2%80%93Howard_correspondence) и [BHK](https://en.wikipedia.org/wiki/Brouwer%E2%80%93Heyting%E2%80%93Kolmogorov_interpretation)
* основан на CIC (calculus of inductive constructions)
  разработанном [Thierry Coquand](https://ru.wikipedia.org/wiki/%D0%9A%D0%BE%D0%BA%D0%B0%D0%BD,_%D0%A2%D1%8C%D0%B5%D1%80%D1%80%D0%B8)
* разработан во Франции при участии [INRIA](https://ru.wikipedia.org/wiki/INRIA "фр. Institut national de recherche en informatique et en automatique, Национальный институт исследований в информатике и автоматике") в 1989г.
* Известные применения
  * Проблема 4х красок 
  * [CompCert](https://en.wikipedia.org/wiki/CompCert)
  * [BB(5)](https://en.wikipedia.org/wiki/Busy_beaver)
    [Up and Atom video](https://www.youtube.com/watch?v=pQWFSj1CXeg)
* Что можно делать
  * доказывать теоремы в т.ч. про алгоритмы и программы
  * писать программы с гарантированными свойствами и извлекать из них программы на некотрых других языках
  * помогать LLM ([пример от OpenAI](https://openai.com/index/formal-math/))
* Другие похожие системы
  * Lean
  * Agda
  * Idris
* [Выпуск](https://podlodka.io/268) подкаста Podlodka про "Формальные методы и верификацию программ"

## Материалы к воркшопу
* [Part01_Programming.v](./Part01_Programming.v) - базовые элементы программирования и самые первые доказательства
* [Part02_Ind.v](./Part02_Ind.v) - простые индуктивные типы и чуть более содержательные доказательства

## Для самостоятельного изучения
* [Software Foundations](https://softwarefoundations.cis.upenn.edu/)
* [Coq in a Hurry](https://cel.hal.science/inria-00001173v4/file/coq-hurry.pdf)
* [Coq'Art](https://www.labri.fr/perso/casteran/CoqArt/)
* [TAPL](https://www.cis.upenn.edu/~bcpierce/tapl/) - Types and Programming Languages

