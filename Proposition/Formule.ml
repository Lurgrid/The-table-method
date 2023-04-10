(** Type des formules. *)
type formule =
  | Bot
  | Top
  | Atome of string
  | Imp of (formule * formule)
  | Ou of (formule * formule)
  | Et of (formule * formule)
  | Non of formule
  (* ajout d'opérateurs étendus *)
  | Xor of (formule * formule)
  | Nor of (formule * formule)
  | Nand of (formule * formule)
  | Diff of (formule * formule)
  | Equiv of (formule * formule)

exception UnknowSymbole of string

(* string_of_formule, Conversion d'une formule en chaîne de caractères. *)
let rec string_of_formule : formule -> string = function
  | Bot -> "⊥"
  | Top -> "T"
  | Atome s -> s
  | Et (f, g) ->
      String.concat ""
        [ "("; string_of_formule f; " ∧ "; string_of_formule g; ")" ]
  | Imp (f, g) ->
      String.concat ""
        [ "("; string_of_formule f; " → "; string_of_formule g; ")" ]
  | Ou (f, g) ->
      String.concat ""
        [ "("; string_of_formule f; " ∨ "; string_of_formule g; ")" ]
  | Non f -> String.concat "" [ "¬"; string_of_formule f ]
  | Diff (f, g) ->
      String.concat ""
        [ "("; string_of_formule f; " \\ "; string_of_formule g; ")" ]
  | Xor (f, g) ->
      String.concat ""
        [ "("; string_of_formule f; " ⊕  "; string_of_formule g; ")" ]
  | Nand (f, g) ->
      String.concat ""
        [ "("; string_of_formule f; " ↑ "; string_of_formule g; ")" ]
  | Nor (f, g) ->
      String.concat ""
        [ "("; string_of_formule f; " ↓ "; string_of_formule g; ")" ]
  | Equiv (f, g) ->
      String.concat ""
        [ "("; string_of_formule f; " ↔ "; string_of_formule g; ")" ]

type interpretation = string -> bool
(** Type des interprétations. *)

(** eval, Évalue une formule en fonction d'une interprétation. *)
let rec eval (i : interpretation) : formule -> bool = function
  | Et (f, g) -> eval i f && eval i g
  | Ou (f, g) -> eval i f || eval i g
  | Imp (f, g) -> (not (eval i f)) || eval i g
  | Diff (f, g) -> eval i f && not (eval i g)
  | Xor (f, g) -> eval i (Diff (f, g)) || eval i (Diff (g, f))
  | Nand (f, g) -> not (eval i (Et (f, g)))
  | Nor (f, g) -> not (eval i (Ou (f, g)))
  | Equiv (f, g) -> eval i (Imp (f, g)) && eval i (Imp (g, f))
  | Non f -> not (eval i f)
  | Atome c -> i c
  | Bot -> false
  | Top -> true
