%*******************************************************************************
%                                    AETOILE
%*******************************************************************************

/*
Rappels sur l'algorithme
 
- structures de donnees principales = 2 ensembles : P (etat pendants) et Q (etats clos)
- P est dedouble en 2 arbres binaires de recherche equilibres (AVL) : Pf et Pu
 
   Pf est l'ensemble des etats pendants (pending states), ordonnes selon
   f croissante (h croissante en cas d'egalite de f). Il permet de trouver
   rapidement le prochain etat a developper (celui qui a f(U) minimum).
   
   Pu est le meme ensemble mais ordonne lexicographiquement (selon la donnee de
   l'etat). Il permet de retrouver facilement n'importe quel etat pendant

   On gere les 2 ensembles de facon synchronisee : chaque fois qu'on modifie
   (ajout ou retrait d'un etat dans Pf) on fait la meme chose dans Pu.

   Q est l'ensemble des etats deja developpes. Comme Pu, il permet de retrouver
   facilement un etat par la donnee de sa situation.
   Q est modelise par un seul arbre binaire de recherche equilibre.

Predicat principal de l'algorithme :

   aetoile(Pf,Pu,Q)

   - reussit si Pf est vide ou bien contient un etat minimum terminal
   - sinon on prend un etat minimum U, on genere chaque successeur S et les valeurs g(S) et h(S)
     et pour chacun
        si S appartient a Q, on l'oublie
        si S appartient a Ps (etat deja rencontre), on compare
            g(S)+h(S) avec la valeur deja calculee pour f(S)
            si g(S)+h(S) < f(S) on reclasse S dans Pf avec les nouvelles valeurs
                g et f 
            sinon on ne touche pas a Pf
        si S est entierement nouveau on l'insere dans Pf et dans Ps
    - appelle recursivement etoile avec les nouvelles valeurs NewPF, NewPs, NewQs

*/

%*******************************************************************************

:- ['avl.pl'].       % predicats pour gerer des arbres bin. de recherche   
:- ['taquin.pl'].    % predicats definissant le systeme a etudier

%*******************************************************************************

main :-
    % initialisations Pf, Pu et Q 
    initial_state(S0),
    heuristique(S0,H0),
    G0 is 0,
    F0 is G0 + H0,
    empty(Pf0),
    empty(Pu0),
    insert([ [F0,H0,G0], S0 ],Pf0,Pf),
    insert([ S0, [F0,H0,G0], nil, nil ], Pu0,Pu),
    
    % lancement de Aetoile
    aetoile(Pf,Pu,[]).



%*******************************************************************************
affiche_solution(nil, _,_).
affiche_solution(Pere, [[Pere,PereEtat,ActionPourEtat]|QReste],[F,H]) :- 
	affiche_solution(PereEtat, QReste,[F,H]),
	write("Action : "), write(ActionPourEtat),
	write("  Etat : "), writeln(Pere),
    write("F      : "), write(F),
    write("H      : "), write(H).

affiche_solution(Pere, [[Etat,_,_]|QReste],_) :-
	Pere \= Etat,
	affiche_solution(Pere, QReste,_).
	


%*******************************************************************************
% Permet de d��velopper un Noeud : R de la forme : [ [NextState,[F,H,G],Umin,A], ... ] en liste
expand(Umin, [_,_,Gu], R) :- findall([NextState,[F,H,G],Umin,A], (rule(A,Cost,Umin,NextState), 
                                                    G is Gu + Cost, 
                                                    heuristique(NextState, H),
                                                    F is G + H), R).

%*******************************************************************************


% Pf0 = situation avant
% Pf1 = nouveau chemin
insert_if_necessary(State, [F,H,G],Umin,A, FPu,_, PuInsereBesoin, _, PfInsertBesoin, Pu1, Pf1) :-
    % si nouveau chemin plus efficace
    FPu > F,
    insert([State, [F,H,G], Umin, A ], PuInsereBesoin, Pu1),
    insert([[F,H,G],State], PfInsertBesoin, Pf1).
    
insert_if_necessary(_, [F,_,_],_,_, FPu,PuAvant, _, PfAvant, _, PuAvant, PfAvant) :-
    % l'ancien chemin est mieux
    FPu =< F.

% on traite chaque noeud successeur avec loop_successors
loop_successors([], _, Pu, Pf, Pu, Pf).

% si State est connu dans Q, alors on oublie cet état et on loop les suivants
loop_successors([[State,_,_,_]| Rest], Q, Pu, Pf, Pu1, Pf1) :- 
	member([State,_,_],Q),!,
    loop_successors(Rest, Q, Pu, Pf, Pu1, Pf1).

% sinon, on verifie si State est dans Pu(et Pf) avec le supress  
% supress renvoie faux si l'��l��ment �� supprimer n'existe pas.
% on appelle ensuite insert_if_necessary pour réinsérer le terme avec la meilleure évaluation
loop_successors([[State,[F,H,G],Umin,A]| Rest], Q, Pu, Pf, Pu1, Pf1) :- 
    suppress(State,Pu,Pu2),!,
    suppress(State, Pf, Pf2),
    insert_if_necessary(State, [F,H,G],Umin,A, Pu, Pu2, Pf, Pf2, Pu3, Pf3),
    loop_successors(Rest, Q, Pu3, Pf3, Pu1, Pf1).  

% sinon State est une nouvelle situation, on insère un nouveau terme dans Pu et Pf.
loop_successors([[State,[F,H,G],Umin,A]| Rest], Q, Pu, Pf, Pu1, Pf1) :- 
    insert([State, [F,H,G], Umin, A ], Pu, PuPrime),
    insert([[F,H,G],State], Pf, PfPrime),
    loop_successors(Rest, Q, PuPrime, PfPrime, Pu1, Pf1).


%*******************************************************************************

% cas 1 : Pf et Pu sont vides, donc pas de solution
aetoile(Pf, Pu, _) :-
    empty(Pf),
    empty(Pu),
    writeln("PAS de SOLUTION : L��ETAT FINAL N��EST PAS ATTEIGNABLE !"),
    fail.

% cas 2 : Si le noeud correspond à un état final, on a donc trouvé une solution et on peut l'afficher
aetoile(Pf, Pu, Qs) :-
	suppress_min([_, Umin], Pf, _),
    suppress([Umin,[F,H,_],Pere,A], Pu, _),
    final_state(Umin),!,
	append([[Umin,Pere,A]],Qs,QResult),
    affiche_solution(Umin, QResult, [F,H]).  % on met le dernier ��tat comme le pere poru forcer l'affichage du dernier etat

% cas 3 (cas général) : on supprime le noeud correspondant à l'état à développer (valeur de F minimale) dans Pf, ainsi que son "frère" 
% dans Pu ; puis on développe l'état U, en déterminant puis traitant chacun des successeurs   
aetoile(Pf, Pu, Qs) :-
    suppress_min([Coutmin, Umin], Pf, Pf1),
    suppress([Umin,_,Pere,A], Pu, Pu1),
    expand(Umin, Coutmin, Successors),
    loop_successors(Successors, Qs, Pu1, Pf1, PuResult, PfResult),
	append([[Umin,Pere,A]],Qs,QResult),
    aetoile(PfResult, PuResult, QResult).
        
    
    
