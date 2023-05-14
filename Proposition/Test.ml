open Formule
open Tableaux
open RandomFormule

(** to_alea_inter : fonction convertissant un témoin de type (string * bool) 
   list en une interprétation, étendant les résultats manquants par des Booléens
   aléatoires. *)
let to_alea_inter (sbl : (string * bool) list) : interpretation =
  let bo =  Random.bool () in 
  let it (sbl : (string * bool) list) (a : string) : bool =
    match List.assoc_opt a sbl with Some x -> x | None -> bo
  in
  it sbl

(** eval_equal : fonction qui evalue la formule f en fonction des témoins de 
    type (string * bool) et qui vérifie que ce résultat est égal au booléan b. *)
let eval_equal (f : formule) (sbl : (string * bool) list) (b : bool) : bool =
  eval (to_alea_inter sbl) f = b

(** ex_sat : fonction qui renvoie si la fonction tableau_ex_sat renvoie le bon 
    résultat pour la formule f. *)
let ex_sat (f : formule) : bool =
  let a = tableau_ex_sat f in
  match a with None -> eval_equal f [] false | Some x -> eval_equal f x true

(** ex_sat : fonction qui renvoie si la fonction tableau_all_sat renvoie le bon 
    résultat pour la formule f. *)
let all_sat (f : formule) : bool =
  let a = tableau_all_sat f in
  match a with
  | [] -> eval (to_alea_inter []) f = false
  | x -> List.for_all (fun x -> eval_equal f x true) x

(** test_valid n réalise :
   — la génération d’une formule aléatoire f avec n opérateurs sur l’alphabet 
      [ "a"; "b"; "c"; "d" ] ;
   — l’affichage de cette formule sur la sortie standard ;
   — la validation des résultats des fonctions tableau_ex_sat et tableau_all_sat 
      de Tableaux.ml, en vérifiant que chaque témoin obtenu peut être converti 
      en une interprétation évaluant la formule f comme vraie et retournant true 
      si tous les résultats sont corrects, false sinon. *)
let test_valid (n : int) : bool =
  let f = random_form [ "a"; "b"; "c"; "d"; "e" ] n in
  Printf.printf "%s\n" (string_of_formule f);
  let a = ex_sat f and b = all_sat f in
  a && b
