
(** val nand : bool -> bool -> bool **)

let nand a b =
  not (if a then b else false)
