open Formule

(** random_atome, atoms renvoie une formule qui est constitué que d'un atome 
   tiré de facon pseudo-aléatoire dans la liste atoms de string supposé non 
   vide. *)
let random_atome : string list -> formule = function
  | [] -> failwith "random_atome : Atoms cannot be empty."
  | atoms -> Atome (List.nth atoms (Random.int (List.length atoms)))

(** random_n_operator, renvoie une formule constitué d'un opérateur nullaire 
   tiré de facon pseudo-aléatoire. *)
let random_n_operator : formule = match Random.int 2 with 0 -> Bot | _ -> Top

(** random_u_operator, renvoie la négation de la formule f. *)
let random_u_operator (f : formule) : formule = Non f

(** random_b_operator, renvoie une formule constitué d'une opération binaire tiré
   de facon pseudo-aléatoire d'opérande f et g. *)
let random_b_operator (f : formule) (g : formule) : formule =
  match Random.int 8 with
  | 0 -> Imp (f, g)
  | 1 -> Ou (f, g)
  | 2 -> Et (f, g)
  | 3 -> Xor (f, g)
  | 4 -> Nor (f, g)
  | 5 -> Nand (f, g)
  | 6 -> Diff (f, g)
  | _ -> Equiv (f, g)

(** random_form atoms k, renvoie une formule pseudo-aléatoire
   avec k opérateurs et des atomes de la liste atoms, liste
   supposée non vide. *)
let rec random_form (atoms : string list) : int -> formule = function
  | 0 -> random_atome atoms
  | 1 -> (
      match Random.int 3 with
      | 0 -> random_n_operator
      | 1 -> random_u_operator (random_atome atoms)
      | _ -> random_b_operator (random_atome atoms) (random_atome atoms))
  | n -> (
      match Random.int 2 with
      | 0 -> random_u_operator (random_form atoms (n - 1))
      | _ ->
          let k = Random.int n in
          random_b_operator (random_form atoms k)
            (random_form atoms (n - k - 1)))
