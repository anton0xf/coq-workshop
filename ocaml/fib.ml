
(** val fib_aux : int -> int -> int -> int **)

let rec fib_aux a b n =
  (fun zero succ n ->
      if n=0 then zero () else succ (n-1))
    (fun _ -> a)
    (fun n' ->
    (fun zero succ n ->
      if n=0 then zero () else succ (n-1))
      (fun _ -> b)
      (fun _ -> fib_aux b (( + ) a b) n')
      n')
    n

(** val nth_fib : int -> int **)

let nth_fib n =
  fib_aux 0 ((fun x -> x + 1) 0) n
