open Formule

(** transform f, renvoie la conversion du dernière opérateur en combinaison de
   négation, de conjonction et de disjonction. *)
let rec transform : formule -> formule = function
  | Imp (f, g) -> Ou (Non f, g)
  | Xor (f, g) -> Ou (Et (f, Non g), Et (Non f, g))
  | Nor (f, g) -> Non (Ou (f, g))
  | Nand (f, g) -> Non (Et (f, g))
  | Diff (f, g) -> Et (f, Non g)
  | Equiv (f, g) -> Ou (Et (f, g), Et (Non f, Non g))
  | Non (Non f) -> f
  | Non Bot -> Top
  | Non Top -> Bot
  | Non f -> Non (transform f)
  | _ as f -> f

(*obliger de retourner couple car sinon le cas de que top dans la formule
   porlbème*)
let rec tab_methode (atoms : formule list) : formule list -> bool * formule list
    = function
  | [] -> (true, atoms)
  | x :: xs -> (
      match x with
      | Bot -> (false, atoms)
      | Top -> tab_methode atoms xs
      | Atome a ->
          if List.exists (fun x -> x = Non (Atome a)) atoms then (false, atoms)
          else tab_methode (x :: atoms) xs
      | Non (Atome a) ->
          if List.exists (fun x -> x = Atome a) atoms then (false, atoms)
          else tab_methode (x :: atoms) xs
      | Et (f, g) -> tab_methode atoms ([ f; g ] @ xs)
      | Non (Ou (f, g)) -> tab_methode atoms ([ Non f; Non g ] @ xs)
      | Ou (f, g) ->
          let a, b = tab_methode atoms ([ f ] @ xs) in
          if a then (a, b) else tab_methode atoms ([ g ] @ xs)
      | Non (Et (f, g)) ->
          let a, b = tab_methode atoms ([ Non f ] @ xs) in
          if a then (a, b) else tab_methode atoms ([ Non g ] @ xs)
      | _ -> tab_methode atoms (transform x :: xs))

let rec foo (atoms : formule list) : formule list -> bool * formule list =
  function
  | [] -> (true, atoms)
  | x :: xs -> (
      match x with
      | Bot -> (false, atoms)
      | Top -> foo atoms xs
      | Atome a ->
          if List.exists (fun x -> x = Non (Atome a)) atoms then (false, atoms)
          else
            foo (if List.exists (( = ) x) atoms then atoms else x :: atoms) xs
      | Non (Atome a) ->
          if List.exists (fun x -> x = Atome a) atoms then (false, atoms)
          else
            foo (if List.exists (( = ) x) atoms then atoms else x :: atoms) xs
      | Et (f, g) -> foo atoms ([ f; g ] @ xs)
      | Non (Ou (f, g)) -> foo atoms ([ Non f; Non g ] @ xs)
      | Ou (f, g) ->
          let a, b = foo atoms ([ f ] @ xs) in
          if a then (a, b) else foo atoms ([ g ] @ xs)
      | Non (Et (f, g)) ->
          let a, b = foo atoms ([ Non f ] @ xs) in
          if a then (a, b) else foo atoms ([ Non g ] @ xs)
      | _ -> foo atoms (transform x :: xs))

(** Teste si une formule est satisfaisable, selon la méthode des tableaux.  *)
let tableau_sat (f : formule) : bool = fst (tab_methode [] [ f ])

let atome_to_sb (lf : formule list) : (string * bool) list =
  List.map
    (fun f ->
      match f with
      | Atome a -> (a, true)
      | Non (Atome a) -> (a, false)
      | _ -> failwith "atome_to_sb : la liste ne contient pas que des Atomes")
    lf

(** Teste si une formule est satisfaisable, renvoyant None si ce n'est pas le
    cas et Some res sinon, où res est une liste de couples (atome, Booléen)
    suffisants pour que la formule soit vraie. *)
let tableau_ex_sat (f : formule) : (string * bool) list option =
  let r = tab_methode [] [ f ] in
  if not (fst r) then None else Some (atome_to_sb (snd r))

(** Renvoie la liste des listes de couples (atome, Booléen) suffisants pour que
      la formule soit vraie, selon la méthode des tableaux.*)
let tableau_all_sat (f : formule) : (string * bool) list list =
  let rec aux (atoms : formule list) = function
    | [] -> [ atome_to_sb atoms ]
    | x :: xs -> (
        match x with
        | Bot -> []
        | Top -> aux atoms xs
        | Atome a ->
            if List.exists (fun x -> x = Non (Atome a)) atoms then []
            else
              aux (if List.exists (( = ) x) atoms then atoms else x :: atoms) xs
        | Non (Atome a) ->
            if List.exists (fun x -> x = Atome a) atoms then []
            else
              aux (if List.exists (( = ) x) atoms then atoms else x :: atoms) xs
        | Et (f, g) -> aux atoms ([ f; g ] @ xs)
        | Non (Ou (f, g)) -> aux atoms ([ Non f; Non g ] @ xs)
        | Ou (f, g) -> aux atoms ([ f ] @ xs) @ aux atoms ([ g ] @ xs)
        | Non (Et (f, g)) ->
            aux atoms ([ Non f ] @ xs) @ aux atoms ([ Non g ] @ xs)
        | _ -> aux atoms (transform x :: xs))
  in
  aux [] [ f ]

let a = Nor (Diff (Atome "b", Atome "c"), Atome "d")
