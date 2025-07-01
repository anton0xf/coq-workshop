
(** val nth_fib_naive : int -> int **)

let rec nth_fib_naive n =
  (fun zero succ n ->
      if n=0 then zero () else succ (n-1))
    (fun _ -> 0)
    (fun n' ->
    (fun zero succ n ->
      if n=0 then zero () else succ (n-1))
      (fun _ -> (fun x -> x + 1) 0)
      (fun n'' -> ( + ) (nth_fib_naive n') (nth_fib_naive n''))
      n')
    n
