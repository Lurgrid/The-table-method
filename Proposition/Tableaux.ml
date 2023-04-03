open Formule

(*------------------------------------------------------------------------------*)
open RandomFormule
(*----------------------d------------------------------------------------------*)

(* transform f renvoie la conversion du dernière opérateur en combinaison de
   négation, de conjonction et de disjonction. *)
(* Et (Ou (f, g), Ou (Non f, Non g)) *)
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

(*obliger de retourner couple car sinon le cas de que top dans la formule porlbème*)
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

(* Teste si une formule est satisfaisable, selon la méthode des tableaux.  *)
let tableau_sat (f : formule) : bool = fst (tab_methode [] [ f ])

(* Teste si une formule est satisfaisable, renvoyant None si ce n'est pas le cas
      et Some res sinon, où res est une liste de couples (atome, Booléen)
      suffisants pour que la formule soit vraie. *)
let tableau_ex_sat (f : formule) : (string * bool) list option =
  let r = tab_methode [] [ f ] in
  if not (fst r) then None
  else
    Some
      (List.map
         (fun f ->
           match f with
           | Atome a -> (a, true)
           | Non (Atome a) -> (a, false)
           | _ -> failwith "sa ne fonctionne pas la")
         (snd r))

(* Renvoie la liste des listes de couples (atome, Booléen) suffisants pour que
      la formule soit vraie, selon la méthode des tableaux.*)
let tableau_all_sat : formule -> (string * bool) list list =
 fun _ -> failwith "to do"

(*---------------------------------------------------------------------------------------------------------*)

(** subst g s f : substitue une formule g à un atome s dans une formule f. *)
let rec subst : formule -> string -> formule -> formule =
 fun g s f ->
  match f with
  | Atome x when x = s -> g
  | Atome _ | Top | Bot -> f
  | Imp (x, y) -> Imp (subst g s x, subst g s y)
  | Ou (x, y) -> Ou (subst g s x, subst g s y)
  | Et (x, y) -> Et (subst g s x, subst g s y)
  | Non x -> Non (subst g s x)
  | _ -> subst g s (transform f)

(** Choisit un atome d'une formule, renvoyant None si aucun n'est présent.*)
let rec choix_atome : formule -> string option =
 fun f ->
  match f with
  | Atome x -> Some x
  | Top | Bot -> None
  | Imp (x, y)
  | Et (x, y)
  | Ou (x, y)
  | Xor (x, y)
  | Nor (x, y)
  | Nand (x, y)
  | Diff (x, y)
  | Equiv (x, y) -> (
      match choix_atome x with None -> choix_atome y | x -> x)
  | Non x -> choix_atome x

(** Simplifie une formule d'une manière paresseuse. *)
let rec simplif_quine : formule -> formule = function
  | f -> (
      match f with
      | (Top | Bot | Atome _) as f -> f
      | Ou (f, g) -> (
          match simplif_quine f with
          | Bot -> simplif_quine g
          | Top -> Top
          | f' -> (
              match simplif_quine g with
              | Bot -> f'
              | Top -> Top
              | g' -> Ou (f', g')))
      | Et (f, g) -> (
          match simplif_quine f with
          | Bot -> Bot
          | Top -> simplif_quine g
          | f' -> (
              match simplif_quine g with
              | Top -> f'
              | Bot -> Bot
              | g' -> Et (f', g')))
      | Imp (f, g) -> (
          match simplif_quine f with
          | Bot -> Top
          | Top -> simplif_quine g
          | f' -> (
              match simplif_quine g with
              | Top -> Top
              | Bot -> Non f'
              | g' -> Imp (f', g')))
      | Diff (f, g) -> (
          match simplif_quine f with
          | Bot -> Bot
          | Top -> simplif_quine (Non g)
          | f' -> (
              match simplif_quine g with
              | Top -> Bot
              | Bot -> f'
              | g' -> Diff (f', g')))
      | Xor (f, g) -> (
          match simplif_quine f with
          | Bot -> simplif_quine g
          | Top -> simplif_quine (Non g)
          | f' -> (
              match simplif_quine g with
              | Top -> simplif_quine (Non f')
              | Bot -> simplif_quine f'
              | g' -> Xor (f', g')))
      | Nor (f, g) -> (
          match simplif_quine f with
          | Bot -> simplif_quine (Non g)
          | Top -> Bot
          | f' -> (
              match simplif_quine g with
              | Top -> Bot
              | Bot -> simplif_quine (Non f')
              | g' -> Nor (f', g')))
      | Nand (f, g) -> (
          match simplif_quine f with
          | Bot -> Top
          | Top -> simplif_quine (Non g)
          | f' -> (
              match simplif_quine g with
              | Top -> simplif_quine (Non f')
              | Bot -> Top
              | g' -> Nand (f', g')))
      | Equiv (f, g) -> (
          match simplif_quine f with
          | Bot -> simplif_quine (Non g)
          | Top -> simplif_quine g
          | f' -> (
              match simplif_quine g with
              | Top -> simplif_quine f'
              | Bot -> simplif_quine (Non f')
              | g' -> Equiv (f', g')))
      | Non f -> (
          match simplif_quine f with Bot -> Top | Top -> Bot | f' -> Non f'))

(** Teste si une formule est satisfaisable, selon l'algorithme de Quine. *)
let rec quine_sat : formule -> bool =
 fun f ->
  match choix_atome f with
  | None -> ( match simplif_quine f with Top -> true | _ -> false)
  | Some a ->
      quine_sat (simplif_quine (subst Top a f))
      || quine_sat (simplif_quine (subst Bot a f))

(** Teste si une formule est une tautologie, selon l'algorithme de Quine. *)
let rec quine_tauto : formule -> bool =
 fun f ->
  match choix_atome f with
  | None -> ( match simplif_quine f with Top -> true | _ -> false)
  | Some a ->
      quine_tauto (simplif_quine (subst Top a f))
      && quine_tauto (simplif_quine (subst Bot a f))

(** Teste si une formule est une contradiction, selon l'algorithme de Quine. *)
let rec quine_contra : formule -> bool =
 fun f ->
  match choix_atome f with
  | None -> ( match simplif_quine f with Top -> false | _ -> true)
  | Some a ->
      quine_contra (simplif_quine (subst Top a f))
      && quine_contra (simplif_quine (subst Bot a f))

(** Teste si une formule est satisfaisable, renvoyant None si ce n'est pas le cas
           et Some res sinon, où res est une liste de couples (atome, Booléen)
           suffisants pour que la formule soit vraie. *)
let rec quine_ex_sat : formule -> (string * bool) list option =
 fun f ->
  match choix_atome f with
  | None -> ( match simplif_quine f with Top -> Some [] | _ -> None)
  | Some a -> (
      match quine_ex_sat (simplif_quine (subst Top a f)) with
      | Some b -> Some ((a, true) :: b)
      | _ -> (
          match quine_ex_sat (simplif_quine (subst Bot a f)) with
          | Some b -> Some ((a, false) :: b)
          | _ -> None))

(** Renvoie la liste des listes de couples (atome, Booléen) suffisants pour que la formule soit vraie,
         selon la formule de Quine. *)
let rec quine_all_sat : formule -> (string * bool) list list =
 fun f ->
  match choix_atome f with
  | None -> ( match simplif_quine f with Top -> [ [] ] | _ -> [])
  | Some a ->
      let b = quine_all_sat (simplif_quine (subst Top a f))
      and c = quine_all_sat (simplif_quine (subst Bot a f)) in
      List.map (List.cons (a, true)) b @ List.map (List.cons (a, false)) c

let rec test y = function
  | 0 -> []
  | n ->
      let f = random_form [ "a"; "b"; "c"; "d"; "e" ] y in
      if quine_sat f <> tableau_sat f then [ f ] else test y (n - 1)

let a = Nor (Diff (Atome "b", Atome "c"), Atome "d")
(* tableau_sat  *)
