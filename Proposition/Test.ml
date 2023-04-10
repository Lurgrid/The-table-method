open Formule
open Tableaux
open RandomFormule

(** to_alea_inter : fonction convertissant un témoin de type (string * bool) 
   list en une interprétation, étendant les résultats manquants par des Booléens
   aléatoires. *)
let to_alea_inter (sbl : (string * bool) list) : interpretation =
  let it (sbl : (string * bool) list) (a : string) : bool =
    match List.assoc_opt a sbl with Some x -> x | None -> Random.bool ()
  in
  it sbl

let bar (f : formule) (sbl : (string * bool) list) (b : bool) : bool =
  eval (to_alea_inter sbl) f = b

let ex_satt (f : formule) : bool =
  let a = tableau_ex_sat f in
  match a with None -> bar f [] false | Some x -> bar f x true

let all_satt (f : formule) : bool =
  let a = tableau_all_sat f in
  match a with
  | [] -> eval (to_alea_inter []) f = false
  | x -> List.for_all (fun x -> bar f x true) x

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
  let a = ex_satt f and b = all_satt f in
  Printf.printf "ex_satt: %b\n" a;
  Printf.printf "all_satt : %b\n" b;
  a && b

(* ⢀⡴⠑⡄⠀⠀⠀⠀⠀⠀⠀⣀⣀⣤⣤⣤⣀⡀⠀⠀⠀⠀⠀⠀⠀⠀⠀⠀⠀⠀
   ⠸⡇⠀⠿⡀⠀⠀⠀⣀⡴⢿⣿⣿⣿⣿⣿⣿⣿⣷⣦⡀⠀⠀⠀⠀⠀⠀⠀⠀⠀
   ⠀⠀⠀⠀⠑⢄⣠⠾⠁⣀⣄⡈⠙⣿⣿⣿⣿⣿⣿⣿⣿⣆⠀⠀⠀⠀⠀⠀⠀⠀
   ⠀⠀⠀⠀⢀⡀⠁⠀⠀⠈⠙⠛⠂⠈⣿⣿⣿⣿⣿⠿⡿⢿⣆⠀⠀⠀⠀⠀⠀⠀
   ⠀⠀⠀⢀⡾⣁⣀⠀⠴⠂⠙⣗⡀⠀⢻⣿⣿⠭⢤⣴⣦⣤⣹⠀⠀⠀⢀⢴⣶⣆
   ⠀⠀⢀⣾⣿⣿⣿⣷⣮⣽⣾⣿⣥⣴⣿⣿⡿⢂⠔⢚⡿⢿⣿⣦⣴⣾⠁⠸⣼⡿
   ⠀⢀⡞⠁⠙⠻⠿⠟⠉⠀⠛⢹⣿⣿⣿⣿⣿⣌⢤⣼⣿⣾⣿⡟⠉⠀⠀⠀⠀⠀
   ⠀⣾⣷⣶⠇⠀⠀⣤⣄⣀⡀⠈⠻⣿⣿⣿⣿⣿⣿⣿⣿⣿⣿⡇⠀⠀⠀⠀⠀⠀
   ⠀⠉⠈⠉⠀⠀⢦⡈⢻⣿⣿⣿⣶⣶⣶⣶⣤⣽⡹⣿⣿⣿⣿⡇⠀⠀⠀⠀⠀⠀
   ⠀⠀⠀⠀⠀⠀⠀⠉⠲⣽⡻⢿⣿⣿⣿⣿⣿⣿⣷⣜⣿⣿⣿⡇⠀⠀⠀⠀⠀⠀
   ⠀⠀⠀⠀⠀⠀⠀⠀⢸⣿⣿⣷⣶⣮⣭⣽⣿⣿⣿⣿⣿⣿⣿⠀⠀⠀⠀⠀⠀⠀
   ⠀⠀⠀⠀⠀⠀⣀⣀⣈⣿⣿⣿⣿⣿⣿⣿⣿⣿⣿⣿⣿⣿⠇⠀⠀⠀⠀⠀⠀⠀
   ⠀⠀⠀⠀⠀⠀⢿⣿⣿⣿⣿⣿⣿⣿⣿⣿⣿⣿⣿⣿⣿⠃⠀⠀⠀⠀⠀⠀⠀⠀
   ⠀⠀⠀⠀⠀⠀⠀⠹⣿⣿⣿⣿⣿⣿⣿⣿⣿⣿⡿⠟⠁⠀⠀⠀⠀⠀⠀⠀⠀⠀
   ⠀⠀⠀⠀⠀⠀⠀⠀⠀⠉⠛⠻⠿⠿⠿⠿⠛⠉ *)
