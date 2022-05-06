type eb = V of int | VRAI | FAUX | AND of eb * eb | OR of eb * eb | XOR of eb * eb | NAND of eb * eb | NOT of eb ;;

(*
 équivalence de AND 
*)
let et a b = match a , b with 
  |FAUX,b -> FAUX
  |VRAI,b-> b 
;;
(*
 équivalence de OR
*)
let ou a b = match a , b with 
  |VRAI,b -> VRAI
  |FAUX,b -> b 
;;
(*
 équivalence de NOT
*)
let non a = match a with 
  |VRAI -> FAUX
  |FAUX -> VRAI 
;;
(*
 équivalence de NAND
*)
let nonet a b = non (et a b)
;;
(*
 équivalence de XOR
*)
let oux a b =  
  if (a==b)
  then FAUX
  else VRAI
;;


let rec appartient ele list = match list with
  | []-> false;
  | tete::queue -> (ele = tete) || (appartient ele queue)
;;

let rec append list1 list2 = match list1 with
  | [] -> list2
  | tete::queue ->
      if (appartient tete list2) then 
        append queue list2
      else tete::(append queue list2)
;;
(* 
  cette fonction prend un membre d'une equation et renvoie la liste de ses
variables 
*)
let rec listVarMembre membre  = match membre with 
  |VRAI -> []
  |FAUX -> []
  | V(i)->[V(i)] 
  | AND(x,y)->append (listVarMembre x) (listVarMembre y)
  | OR(x,y)->append (listVarMembre x) (listVarMembre y)
  | NAND(x,y)->append (listVarMembre x) (listVarMembre y)
  | XOR(x,y)->append (listVarMembre x) (listVarMembre y)
  | NOT(x)->(listVarMembre x)
;;

(* 
  cette fonction prend un systeme d'equations et renvoie la liste de ses
variables 
*)

let rec ens_var l = match l with
  | [] -> [] 
  | [[a;b]] -> append (listVarMembre a) (listVarMembre b)
  | h::q -> append (ens_var [h]) (ens_var q ) 
;;

(*
  elle prend le nombre total de variables, et renvoie les combinaions de 
valeurs possibles 

*)

let rec combi n a =
  if n = 0 then [[]]
  else
    let res = combi (n-1) a in
    List.concat (List.map (fun m -> List.map(fun s -> s@m) a) res);;
(*
 cette fonction associe à chaque variable une valueur possible 
*)
let rec associerVarSolu combinaison listVariables = match combinaison with 
  |[] -> []
  |head::tail -> (List.combine listVariables head )::(associerVarSolu tail listVariables)
;; 

(* 
  cette fonction renvoie toutes les possibilités 
*)
let possibilite sys =  
  associerVarSolu (combi (List.length (ens_var sys)) [[FAUX];[VRAI]]) (ens_var sys);;

;;
(*dans notre programme, les équations vont être présentées comme suit:
                         une liste de deux éléments [a;b] dont a représente le membre gauche de l'équation,
 et b son membre droit. 
*)

(* cette fonction evalue un membre et dit s'il est VRAI ou FAUX 
   si toutes les variables de membre sont initialisées à une valeur*)
let rec evaluer membre = match membre with 
  |V(i)->failwith " V(i) est une variable "
  |VRAI -> VRAI
  |FAUX -> FAUX
  |AND(a,b)->et (evaluer a) (evaluer b)
  |OR(a,b) -> ou (evaluer a) (evaluer b)
  |NAND(a,b) -> nonet (evaluer a) (evaluer b)
  |XOR(a,b)-> oux (evaluer a) (evaluer b)
  |NOT(a) ->non (evaluer a)
;;

(*cette fonction prend un membre et remplace les V(i) par valeur *)
let rec remplacerValeurMembre (V(i)) valeur membre = match membre with 
  |VRAI -> VRAI
  |FAUX-> FAUX 
  |V(j)-> if(i==j) then valeur else V(j)
  |x->
      (
        match x with 
        |AND(a,b)->AND((remplacerValeurMembre (V(i)) valeur a),(remplacerValeurMembre (V(i)) valeur b))
        |OR(a,b) -> OR((remplacerValeurMembre (V(i)) valeur a),(remplacerValeurMembre (V(i)) valeur b))
        |NAND(a,b) -> NAND((remplacerValeurMembre (V(i)) valeur a),(remplacerValeurMembre (V(i)) valeur b))
        |XOR(a,b)->XOR((remplacerValeurMembre (V(i)) valeur a),(remplacerValeurMembre (V(i)) valeur b))
        |NOT(a) -> NOT(remplacerValeurMembre (V(i)) valeur a)
      )
;;
          

(* cette fonction prend une equation, et remplace les V(i) par valeur en se servant 
   de la fonction remplacerValeurMembre *) 
let remplacerValeurEquation (V(i)) valeur equation = match equation with
  |[] -> []
  |[x;y]-> [remplacerValeurMembre (V(i)) valeur x; remplacerValeurMembre (V(i)) valeur y]
;;

(* cette fonction sert à evaluer l'equation si elle est vraie ou fausse 
   NOTEZ QUE : il faut d'abord initialiser toutes les variables de cette equation 
   pour pouvoir l'évaluer sinon ça renverra une erreur *)
let evalequation eq = match eq with
  |[]->false
  |[x;y]-> if((evaluer x)==(evaluer y))
      then true
      else false
;;



(*
  cette fonction elle prend une solution et une equation et remplacer 
les variables de l'equation par les valeurs de la solution 
*) 

let rec remplacerSolution solution equation = match solution with
  |[]-> []
  |[(V(i),valeur)]-> remplacerValeurEquation (V(i)) valeur equation
  |(V(i), valeur)::tail -> remplacerValeurEquation (V(i)) valeur (remplacerSolution tail equation)
;;

(*  
  cette fonction prend une solution et un systeme, et renvoie true 
 si la solution est valable, false sinon
*)

let rec verifSolution solution system = match system with
  |[]->true
  |equation::tail ->if((evalequation (remplacerSolution solution equation)) == false)
      then false
      else verifSolution solution tail
;; 

(* 
  cette fonction prends une liste de solutions possibles et un système d'équation
et renvoie une liste de solutions valable
*)

let rec verificationFinale listSolution system = match listSolution with 
  |[]->[]
  |solution::tail -> if(verifSolution solution system)
      then solution::(verificationFinale tail system)
      else verificationFinale tail system
;;
let equation = [OR(V(1),V(2));VRAI];; 
let equation2 = [XOR(V(1),V(3));V(2)];; 
let equation3 = [NAND(V(1),AND(V(2),V(3)));VRAI];;
let system = [equation;equation2;equation3];; 

let pos = possibilite system;;
verificationFinale pos system;;



