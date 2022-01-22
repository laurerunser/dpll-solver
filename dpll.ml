open List

(* fonctions utilitaires *********************************************)
(* filter_map : ('a -> 'b option) -> 'a list -> 'b list
   disponible depuis la version 4.08.0 de OCaml dans le module List :
   pour chaque élément de `list', appliquer `filter' :
   - si le résultat est `Some e', ajouter `e' au résultat ;
   - si le résultat est `None', ne rien ajouter au résultat.
   Attention, cette implémentation inverse l'ordre de la liste *)
let filter_map filter list =
  let rec aux list ret =
    match list with
    | []   -> ret
    | h::t -> match (filter h) with
      | None   -> aux t ret
      | Some e -> aux t (e::ret)
  in aux list []

(* print_modele : int list option -> unit
   affichage du résultat *)
let print_modele: int list option -> unit = function
  | None   -> print_string "UNSAT\n"
  | Some modele -> print_string "SAT\n";
     let modele2 = sort (fun i j -> (abs i) - (abs j)) modele in
     List.iter (fun i -> print_int i; print_string " ") modele2;
     print_string "0\n"

(* ensembles de clauses de test *)
let exemple_3_12 = [[1;2;-3];[2;3];[-1;-2;3];[-1;-3];[1;-2]]
let exemple_7_2 = [[1;-1;-3];[-2;3];[-2]]
let exemple_7_4 = [[1;2;3];[-1;2;3];[3];[1;-2;-3];[-1;-2;-3];[-3]]
let exemple_7_8 = [[1;-2;3];[1;-3];[2;3];[1;-2]]
let systeme = [[-1;2];[1;-2];[1;-3];[1;2;3];[-1;-2]]
let coloriage = [[1;2;3];[4;5;6];[7;8;9];[10;11;12];[13;14;15];[16;17;18];[19;20;21];[-1;-2];[-1;-3];[-2;-3];[-4;-5];[-4;-6];[-5;-6];[-7;-8];[-7;-9];[-8;-9];[-10;-11];[-10;-12];[-11;-12];[-13;-14];[-13;-15];[-14;-15];[-16;-17];[-16;-18];[-17;-18];[-19;-20];[-19;-21];[-20;-21];[-1;-4];[-2;-5];[-3;-6];[-1;-7];[-2;-8];[-3;-9];[-4;-7];[-5;-8];[-6;-9];[-4;-10];[-5;-11];[-6;-12];[-7;-10];[-8;-11];[-9;-12];[-7;-13];[-8;-14];[-9;-15];[-7;-16];[-8;-17];[-9;-18];[-10;-13];[-11;-14];[-12;-15];[-13;-16];[-14;-17];[-15;-18]]

(********************************************************************)
              
(* simplifie : int -> int list list -> int list list 
   Applique la simplification de l'ensemble des clauses en mettant
   le littéral i à vrai *)
let simplifie i clauses =
  let rec delete_literal_from_clause i clause =
    if mem i clause then None
    else if mem (-i) clause then Some (filter (fun x -> x != (-i)) clause)
    else Some clause in
  filter_map (fun c -> delete_literal_from_clause i c) clauses


(* solveur_split : int list list -> int list -> int list option
   Exemple d'utilisation de `simplifie' *)
(* Cette fonction ne doit pas être modifiée, sauf si vous changez 
   le type de la fonction simplifie *)
let rec solveur_split clauses interpretation =
  (* l'ensemble vide de clauses est satisfiable *)
  if clauses = [] then Some interpretation else
  (* un clause vide est insatisfiable *)
  if mem [] clauses then None else
  (* branchement *) 
  let l = hd (hd clauses) in
  let branche = solveur_split (simplifie l clauses) (l::interpretation) in
  match branche with
  | None -> solveur_split (simplifie (-l) clauses) ((-l)::interpretation)
  | _    -> branche

(* unitaire : int list list -> int
  - si `clauses' contient au moins une clause unitaire, retourne
    le littéral de cette clause unitaire ;
  - sinon, renvoie None *)
let rec unitaire (clauses : int list list) =
  match clauses with
  | [] -> None
  | c::cx -> if List.length c = 1 then Some (hd c)
             else unitaire cx

   
(* Pour comparer les propositions lors de l'utilisation de List.sort_uniq :
   - return 0 if x = y
   - 1 if abs x > abs y 
   - -1 if abs x < abs y *)
let compare x y =
  let x' = abs x in let y' = abs y in
  if x = y then 0 else if x' > y' then 1 else -1


(* get_literals int list list -> int list
   Renvoie la liste de tous les littéraux contenus dans la formule.
   Un litéral et sa négation sont considérés comme 2 littéraux différents *)
let get_literals clauses =
  List.sort_uniq compare (List.flatten clauses)

(* pur : int list list -> int
   Renvoie un littéral pur de `clauses` ou None si elles n'en contiennent pas *)
let pur clauses =
  let list_literals = get_literals clauses in  
  let rec pur_rec literals p =  
    match literals with
    | [] -> None
    | x::xs -> if not (mem (-x) p) then Some x else pur_rec xs p
  in pur_rec list_literals list_literals

(* solveur_dpll_rec : int list list -> int list -> int list option *)
let rec solveur_dpll_rec clauses interpretation =
  if clauses = [] then Some interpretation (* pas de clauses = SAT *)
  else if mem [] clauses then None (* clause vide = UNSAT *)
  else
    match unitaire clauses with
    | Some u -> solveur_dpll_rec (simplifie u clauses) (u::interpretation)
    | None ->
       match pur clauses with
       | Some p -> solveur_dpll_rec (simplifie p clauses) (p::interpretation)
       | None ->
          let l = hd (hd clauses) in
          let branche = solveur_dpll_rec (simplifie l clauses) (l::interpretation) in
          match branche with
          | None -> solveur_dpll_rec (simplifie (-l) clauses) ((-l)::interpretation)
          | _    -> branche
      
let () =
  let clauses = Dimacs.parse Sys.argv.(1) in
  print_modele (solveur_dpll_rec clauses [])
