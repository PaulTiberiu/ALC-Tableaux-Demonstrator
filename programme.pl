/*
Realise par:

SAID Faten Racha
IORDACHE Paul-Tiberiu
*/




/*
######################################################################
#                                                                    #
#          Predicats de mise sous forme normale negative             #
#                                                                    #
######################################################################
*/

nnf(not(and(C1,C2)),or(NC1,NC2)):- nnf(not(C1),NC1), nnf(not(C2),NC2),!.
nnf(not(or(C1,C2)),and(NC1,NC2)):- nnf(not(C1),NC1), nnf(not(C2),NC2),!.
nnf(not(all(R,C)),some(R,NC)):- nnf(not(C),NC),!.
nnf(not(some(R,C)),all(R,NC)):- nnf(not(C),NC),!.
nnf(not(not(X)),Y):- nnf(X,Y),!.
nnf(not(X),not(X)):-!.
nnf(and(C1,C2),and(NC1,NC2)):- nnf(C1,NC1),nnf(C2,NC2),!.
nnf(or(C1,C2),or(NC1,NC2)):- nnf(C1,NC1), nnf(C2,NC2),!.
nnf(some(R,C),some(R,NC)):- nnf(C,NC),!.
nnf(all(R,C),all(R,NC)) :- nnf(C,NC),!.
nnf(X,X).


/*Concatener les deux listes L1 et L2 et renvoier la liste L3*/

concat([],L1,L1).
concat([X|Y],L1,[X|L2]) :- concat(Y,L1,L2).


/*Supprimer X de la liste L1 et renvoier la liste resultante dans L2*/

enleve(X,[X|L],L) :-!.
enleve(X,[Y|L],[Y|L2]) :- enleve(X,L,L2).


/*Generer un nouvel identificateur qui est fourni en sortie dans Nom*/
compteur(1).
genere(Nom) :- compteur(V),nombre(V,L1),
                concat([105,110,115,116],L1,L2),
                V1 is V+1,
                dynamic(compteur/1),
                retract(compteur(V)),
                dynamic(compteur/1),
                assert(compteur(V1)),nl,nl,nl,
                name(Nom,L2).
nombre(0,[]).
nombre(X,L1) :- R is (X mod 10), 
                Q is ((X-R)//10),
                chiffre_car(R,R1),
                char_code(R1,R2),
                nombre(Q,L),
                concat(L,[R2],L1).

chiffre_car(0,'0').
chiffre_car(1,'1').
chiffre_car(2,'2').
chiffre_car(3,'3').
chiffre_car(4,'4').
chiffre_car(5,'5').
chiffre_car(6,'6').
chiffre_car(7,'7').
chiffre_car(8,'8').
chiffre_car(9,'9').



/*
######################################################################
#                                                                    #
#              Definition de la TBox et de la ABox                   #
#                                                                    #
######################################################################
*/


/* Concepts atomiques, roles et instances*/

/*Predicats pour les concepts atomiques*/
cnamea(personne).
cnamea(livre).
cnamea(objet).
cnamea(sculpture).
cnamea(anything).
cnamea(nothing).

/*Predicats pour les concepts non atomiques*/
cnamena(auteur).
cnamena(editeur).
cnamena(sculpteur).
cnamena(parent).

/*Predicats pour les instances*/
iname(michelAnge).
iname(david).
iname(sonnets).
iname(vinci).
iname(joconde).

/*Predicats pour les roles*/
rname(aCree).
rname(aEcrit).
rname(aEdite).
rname(aEnfant).


/*TBox*/

equiv(sculpteur,and(personne,some(aCree,sculpture))).
equiv(auteur,and(personne,some(aEcrit,livre))).
equiv(editeur,and(personne,and(not(some(aEcrit,livre)),some(aEdite,livre)))).
equiv(parent,and(personne,some(aEnfant,anything))).


/*ABox*/

/*Predicats pour les instantiations de concepts*/
inst(michelAnge,personne).
inst(david,sculpture).
inst(sonnets,livre).
inst(vinci,personne).
inst(joconde,objet).

/*Predicats pour les instantiations de roles*/
instR(michelAnge, david, aCree).
instR(michelAnge, sonnets, aEcrit).
instR(vinci, joconde, aCree).


/*
######################################################################
#                                                                    #
#                          PARTIE 1                                  #
#                                                                    #
#######################################################################
*/




/*1.---------------------------- Verification de la correction semantique ----------------------------*/


/*Semantique est a vrai si elle verifie que tout identificateur de concept, d'instance, de role en est bien un et qu'ils sont uniques */
semantique :- setof(Ca, cnamea(Ca), ListeConceptsAtomiques),
            setof(Cna, cnamena(Cna), ListeConceptsNonAtomiques),
            setof(R, rname(R), ListeRoles),
            setof(I, iname(I), ListeInstances),
            append(ListeConceptsAtomiques, ListeConceptsNonAtomiques, L1),
            append(ListeRoles, ListeInstances, L2),
            append(L1, L2, L), 
            unique(L).


/* Verifier le cas de base la liste vide est unique ou qu'on test sur un seul element*/
unique([]).
/*sinon, faire unique([X])*/
unique(_ | []).
/* Verifier l'unicite des elements pour la tete de la liste*/
unique([X | L]) :-
    /* Verifier que X n'est pas dans L*/
    not(member(X, L)), 
    /*recursion*/
    unique(L).


/*2.---------------------------- Verification syntaxique ----------------------------*/



/*---- Concepts atomiques et non atomiques ----*/
/*Un concept est valide que s'il est atomique ou non atomique*/
syntaxeConcept(X) :- cnamea(X).
syntaxeConcept(X) :- cnamena(X).
/*Ajouter les identificateurs anything et nothing qui correspondent respectivement a ⊤ et ⊥*/
nothing(X) :- cnamea(X).
anything(X) :- cnamea(X).

/*Instances*/
/*Une instance I est valide que s'il existe un identificateur d'instance associe a cette instance*/
instance(I) :- iname(I).

/*Role*/
/*Un role R est valide que s'il existe un identificateur de role associe a ce role*/
role(R) :- rname(R).

/*Grammaire*/
:- discontiguous syntaxeConcept/1.
syntaxeConcept(not(C)) :- syntaxeConcept(C).
syntaxeConcept(and(C1, C2)) :- syntaxeConcept(C1), syntaxeConcept(C2).
syntaxeConcept(or(C1, C2)) :- syntaxeConcept(C1), syntaxeConcept(C2).
syntaxeConcept(some(R, C)) :- role(R), syntaxeConcept(C).
syntaxeConcept(all(R, C)) :- role(R), syntaxeConcept(C).



/*---- Verification syntaxique de la TBox et ABox ----*/

/*Construction des listes de TBox et ABox*/
/*TBox contient les definitions
Notons que dans Tbox on ne represente pas de relations de subsumption par souci de simplification (enoncé)*/
listeTBox(TBox) :- setof((Concept_g, Def), equiv(Concept_g, Def), TBox).
/*ABoxConcept contient les assertions de concepts*/
listeABoxConcept(ABoxConcept) :- setof((Instance, Concept), inst(Instance, Concept), ABoxConcept).
/*ABoxRole contient les assertions de roles*/
listeABoxRole(ABoxRole) :- setof((Instance1, Instance2, Role), instR(Instance1, Instance2, Role), ABoxRole).



/*--- Verifier la syntaxe de ABox ---*/

/**Cas1 : ABoxConcept contient les assertions de concepts*/
verifierInst(Instance, Concept) :- instance(Instance), syntaxeConcept(Concept).

/*Cas de base ou la ABox est vide*/
syntaxeABoxConcept([]).
/*Verifier que chaque element de la ABoxConcept est une assertion de concept valide */
syntaxeABoxConcept([(Instance, Concept) | L]) :- verifierInst(Instance, Concept) , 
                                                    syntaxeABoxConcept(L).

/*Cas2 : ABoxRole contient les assertions de roles*/
verifierInstR(Instance1, Instance2, Role) :- instance(Instance1), instance(Instance2), role(Role).
/*Cas de base ou la ABox est vide*/
syntaxeABoxRole([]).
/*Verifier que chaque element de la ABoxRole est une assertion de role valide */
syntaxeABoxRole([(Instance1, Instance2, Role) | L]) :- 
    verifierInstR(Instance1, Instance2, Role), 
    syntaxeABoxRole(L).


/*Pour avoir syntaxeABox a true Il faut que les 2 cas precedents soient verifies*/
syntaxeABox(ABoxConcept, ABoxRole) :- syntaxeABoxConcept(ABoxConcept),
                                    syntaxeABoxRole(ABoxRole).






/*--- Verifier la syntaxe de TBox ---*/
/*Il faut que le concept soit non atomique pour pouvoir le mettre dans la TBox*/
verifierEquiv(Concept_g, Def) :- cnamena(Concept_g), syntaxeConcept(Def).
/*Cas de base ou la TBox est vide*/
syntaxeTBox([]).
/*Verifier que chaque element de la TBox est une equivalence (definition) valide */
syntaxeTBox([(Concept_g, Def) | L]) :- verifierEquiv(Concept_g, Def), syntaxeTBox(L).




/*--- Verifier la syntaxe generale ---*/

syntaxe(TBox, ABoxConcept, ABoxRole) :- syntaxeTBox(TBox),
                                        syntaxeABox(ABoxConcept, ABoxRole).


/*-------------------- concept : Verification de la correction semantique et de la correction syntaxique --------------------*/
/*concept est a true si la semantique et la syntaxe sont correctes*/

concept :-  (semantique -> nl, write("La correction semantique est verifiee"); nl, write("*** Erreur: La correction semantique n'est pas verifiee"), nl, fail),
            listeTBox(TBox),
            listeABoxConcept(ABoxConcept),
            listeABoxRole(ABoxRole),
            (syntaxe(TBox, ABoxConcept, ABoxRole) -> nl, write("La correction syntaxique est verifiee"); nl, write("*** Erreur: La correction syntaxique n'est pas verifiee"), nl, fail).



/*3.---------------------------- Verification l'autoreference ----------------------------*/

/*Cas ou la definition est un concept atomique: rien à verifier on est sur qu'il n'y a pas de cycle*/
/*_ ici est un Concept*/
pasAutoRef_element(_, Def) :- cnamea(Def). 

/*Cas ou la definition est un concept non atomique: 1. verifier qu'il n'est pas unifiable avec le concept gauche et 2. recuperer la definition de la definition puis 
3. Appliquer la recursivite pour s'assurer qu'il n'y a pas de cycle en partant cette fois de la definition de la definition*/
pasAutoRef_element(Concept, Def) :- cnamena(Def), Concept \= Def, equiv(Def, Def2), pasAutoRef_element(Concept, Def2).

/*Traiter les differents cas possibles de Def (definition d'un concept)*/
pasAutoRef_element(Concept, and(Def1, Def2)) :- pasAutoRef_element(Concept, Def1), pasAutoRef_element(Concept, Def2).
pasAutoRef_element(Concept, or(Def1, Def2)) :- pasAutoRef_element(Concept, Def1), pasAutoRef_element(Concept, Def2).
pasAutoRef_element(Concept, not(Def1)) :- pasAutoRef_element(Concept, Def1).
/*_ ici est un role*/
pasAutoRef_element(Concept, some(_, C)) :- pasAutoRef_element(Concept, C).
pasAutoRef_element(Concept, all(_, C)) :- pasAutoRef_element(Concept, C).

/*Cas de base*/
pasAutoRef_list([]). 
/*Cas general : prend en entree la TBox sous forme de liste*/
pasAutoRef_list([(Concept, Def)| L]) :- pasAutoRef_element(Concept, Def), pasAutoRef_list(L). 
/*Note : avoir un (Concept, Def) dans la liste de la TBox signifie Concept equivalent a Def*/



/*-------------------- pas_autoref : Verification generale de l'autoreference --------------------*/

/*Verification de l'existance d'une auto-reference (d'un cycle) dans le fichier fourni*/
pas_autoref :- listeTBox(TBox), pasAutoRef_list(TBox).


/*4.---------------------------- Traitement TBox ----------------------------*/

/*remplacer(...) a pour objectif de remplacer par une expression ou ne figurent plus que des identificateurs de concepts atomiques*/

/*Cas ou Concept est atomique : ne rien faire c'est a dire le remplacer par lui meme */ 
remplacer(Concept, Concept) :- cnamea(Concept).

/*Cas ou Concept est non atomique : recuperer Def2 (sa definition) est appliquer une recursivite dessus de sorte a etre sur que Def2 peut en effet etre remplace par Def */ 
remplacer(Concept, Def) :- cnamena(Concept), equiv(Concept, Def2), remplacer(Def2, Def).

/*Traiter les differents cas possibles de remplacer(Def1,Def2)*/
remplacer(not(Concept), not(Def)) :- remplacer(Concept, Def).
remplacer(and(Concept1, Concept2), and(Def1, Def2)) :- remplacer(Concept1, Def1), remplacer(Concept2, Def2).
remplacer(or(Concept1, Concept2), or(Def1, Def2)) :- remplacer(Concept1, Def1), remplacer(Concept2, Def2).
remplacer(all(Role1, Concept), all(Role2,Def)) :- Role1 = Role2, remplacer(Concept,Def). 
remplacer(some(Role1, Concept), some(Role2,Def)) :- Role1 = Role2, remplacer(Concept,Def). 


/*Cas de base*/
remplacer_liste_TBox([], []).

/*Cas ou on doit remplacer une liste Tbox par sa version nnf simplifiee (soit ou ne figurent plus que des identificateurs de concepts atomiques et 
qui a ete mise sous forme normale negative) : 
traiter le premier element de la liste Tbox : remplacer Def1 par Def2 si en simplifiant Def1 et en appliquant la NNF a Def on tombe sur Def2, 
faire appel a la recursivite pour traiter le reste des elements de la liste de la TBox*/
remplacer_liste_TBox([(C1, Def1) | L1], [(C1, Def2) | L2]) :- remplacer(Def1, Def), 
                                                            nnf(Def, Def2),
                                                            remplacer_liste_TBox(L1, L2).

/*traitement_Tbox retourne true si elle est appliquee a la TBox ecrite sous forme normale negative*/
traitement_TBox(NNF_TBox) :- listeTBox(TBox),nl,nl,
                            write("-- TBox avant simplification et mise sous NNF= "),nl, write(TBox),nl,nl,
                            remplacer_liste_TBox(TBox, NNF_TBox),
                            write("-- TBox apres simplification et mise sous  NNF = "),nl, write(NNF_TBox),nl,nl.



/*5 .---------------------------- Traitement ABox ----------------------------*/

/* --- Verifier si un concept (definit pour une certaine instance dans la ABox) est dans la TBox finale (simplifiee et mise sous nnf) --- */
/*Cas ou le concept est en tete de liste de la TBox*/
/*_ ici c'est la suite d'une liste L*/
verifier_concept_dans_TBox(Concept, Def, [(C1, Def1) | _] ) :- Concept = C1, Def = Def1.
/*Cas ou le concept n'est pas en tete de liste de la TBox, soit appliquer une recursivite sur les elements restants de la liste */
verifier_concept_dans_TBox(Concept, Def, [(C1, Def1) | L] ) :- Concept \= C1, verifier_concept_dans_TBox(Concept, Def, L).
/*Note : verifier_concept_dans_TBox retourne true si Def est bien la definition simplifiee est mise sous forme normale negative de Concept, qu'on retrouve dans la TBox simplifiee et mise sous nnf*/


/*Cas de base*/
remplacer_liste_ABox([], []).

/*Cas ou le concept d'une instance de la ABox est atomique : (ne rien faire) passer au prochain element de la liste ABox*/
remplacer_liste_ABox([(Inst, Concept) | L1], [(Inst, Concept) | L2]) :- cnamea(Concept), remplacer_liste_ABox(L1, L2).

/*Cas ou le concept d'une instance de la ABox est non atomique : 
remplacer Concept par Def qui est sa definition simplifiee et mise sous nnf (qu'on recuperer à partir de la TBox traitee) 
puis passer au prochain element de la liste ABox*/
remplacer_liste_ABox([(Inst, Concept) | L1], [(Inst, Def) | L2]) :- cnamena(Concept), 
                                                                    traitement_TBox(NNF_TBox),
                                                                    verifier_concept_dans_TBox(Concept, Def, NNF_TBox),
                                                                    remplacer_liste_ABox(L1, L2).

/*traitement_ABox retourne true si elle est appliquee a la ABox simplifiee et ecrite sous forme normale negative*/
traitement_ABox(NNF_ABox) :- listeABoxConcept(ABoxConcept),
                            nl,write("-- Abi avant simplification et mise sous NNF = "),nl, write(ABoxConcept),nl,
                            remplacer_liste_ABox(ABoxConcept, NNF_ABox),nl,
                            write("-- Abi apres simplification et mise sous NNF = "),nl, write(NNF_ABox),nl,nl.
/*Note : pour verifier la coherence d'une ABox il est inutile de traiter le cas des assertions de roles car un role ne peut etre ni simplifie ni mis sous nnf*/


/*-------------------- partie1 : Verification de la coherence de toute la premiere partie --------------------*/

premiere_etape(TBox, Abi, Abr) :- concept,
                                (pas_autoref -> nl, write("Pas d'autoreference"); nl, write("*** Erreur: Autoreference detectee"), nl, fail),
                                traitement_TBox(TBox),
                                traitement_ABox(Abi),
                                /*aucun traitement particulier a appliquer sur Abr, il suffit de verifier qu'elle contient exactement les instances de roles definies dans le fichier en verifiant que ces derniers verifient bien la syntaxe d'une instanciation de role*/
                                listeABoxRole(Abr),
                                nl,write("-- Abr = "),nl, write(Abr),nl,nl.



/*
######################################################################
#                                                                    #
#                          PARTIE 2                                  #
#                                                                    #
#######################################################################
*/



deuxieme_etape(Abi,Abi1,Tbox) :- saisie_et_traitement_prop_a_demontrer(Abi,Abi1,Tbox).

saisie_et_traitement_prop_a_demontrer(Abi,Abi1,Tbox) :-
    nl,write("Entrez le numero du type de proposition que vous voulez demontrer :"),nl,
    write("1 Une instance donnee appartient a un concept donne."),nl,
    write("2 Deux concepts n'ont pas d'elements en commun(ils ont une intersection vide)."),nl, 
    read(R), 
    suite(R,Abi,Abi1,Tbox).

suite(1,Abi,Abi1,Tbox) :- acquisition_prop_type1(Abi,Abi1,Tbox),!.

suite(2,Abi,Abi1,Tbox) :- acquisition_prop_type2(Abi,Abi1,Tbox),!.

suite(R,Abi,Abi1,Tbox) :- nl,write('Cette reponse est incorrecte.'),nl,
                          saisie_et_traitement_prop_a_demontrer(Abi,Abi1,Tbox).


/*--------------Acquisition d'une proposition de type 1--------------*/
get_prop_type1(Instance, Concept) :- write("--Traiter une proposition de type1--"),nl,
                                    write("Veuillez introduire l'identificateur de l'instance :"), nl, read(Instance),
                                    write("Veuillez introduire l'identificateur du concept ou sa definition :"), nl, read(Concept), nl,
                                    /*afficher une erreur si les informations entrees par l'utilisateur sont syntaxiquement incorrects*/
                                    (verifierInst(Instance, Concept);
                                    write("Error : syntaxe de la ABox non respectee, l'instance ou le concept introduit n'est pas defini"),nl, fail).

/*Simplifier Concept, recuperer sa negation et mettre sous nnf*/
traitement_prop_type1((Instance, Concept), (Instance, New_Concept)):- remplacer(not(Concept), Not_Concept_simplifie),
                                                                        nnf(Not_Concept_simplifie, New_Concept),
                                                                        write("Nouveau concept simplifie et mis sous nnf : "), write(New_Concept),nl.
/*Note : le resultat de cette etape est de construire un nouveau element (Instance, New_Concept) pour lequel New_Concept est la negation de Concept simplifie qu'on met sous nnf*/

acquisition_prop_type1(Abi, Abi1, TBox) :- get_prop_type1(Instance, Concept),
                                         traitement_prop_type1((Instance, Concept), (Instance, New_Concept)),
                                         /*ajouter (Instance, new_Concept) a la ABox*/
                                         concat(Abi,[(Instance, New_Concept)], Abi1),
                                         write("Abi1 : "), write(Abi1), nl.
                                         

/*--------------Acquisition d'une proposition de type 2--------------*/
get_prop_type2(Concept1, Concept2) :- write("--Traiter une proposition de type2--"),nl,
                                    write("Veuillez introduire l'identificateur du premier concept ou sa definition :"), nl, read(Concept1),
                                    write("Veuillez introduire l'identificateur du deuxieme concept ou sa definition :"), nl, read(Concept2),
                                    /*afficher une erreur si les informations entrees par l'utilisateur sont syntaxiquement incorrects*/
                                    (syntaxeConcept(and(Concept1, Concept2));
                                    write("*** Erreur : syntaxe de la ABox non respectee, au moins un des deux concepts introduits n'est pas defini"),nl, fail).

/*Simplifier les deux concepts et les mettre sous nnf*/
traitement_prop_type2(and(Concept1, Concept2), (Instance, and(New_Concept1, New_Concept2))):- remplacer(Concept1, Concept1_simplifie),
                                                                                        remplacer(Concept2, Concept2_simplifie),
                                                                                        nnf(Concept1_simplifie, New_Concept1),
                                                                                        nnf(Concept2_simplifie, New_Concept2), nl,
                                                                                        write("Concept1 simplifie et mis sous nnf : "), write(New_Concept1),nl,
                                                                                        write("Concept2 simplifie et mis sous nnf : "), write(New_Concept2),nl.
/*Note : le resultat de cette etape est de creer une nouvelle instance qui est une conjonction des deux nouveaux concepts resultant de la simplification et la mise sous nnf des concepts introduits par l'utilisateur*/

acquisition_prop_type2(Abi,Abi1,Tbox) :- get_prop_type2(Concept1, Concept2),
                                         genere(Instance),
                                         traitement_prop_type2(and(Concept1, Concept2), (Instance, and(New_Concept1, New_Concept2))),
                                         /*ajouter (Instance, and(new_Concept1, new_Concept2)) a la ABox*/
                                         concat(Abi,[(Instance, and(New_Concept1, New_Concept2))], Abi1),
                                         write("Abi1: "), write(Abi1), nl.


/*
######################################################################
#                                                                    #
#                          PARTIE 3                                  #
#                                                                    #
######################################################################
*/


troisieme_etape(Abi,Abr) :- tri_Abox(Abi,Lie,Lpt,Li,Lu,Ls),
                            resolution(Lie,Lpt,Li,Lu,Ls,Abr),
                            nl,write('Youpiiiiii, on a demontre la proposition initiale !!!').
                             
/*tri_Abox : A partir de la liste des assertions de concepts de la Abox etendue 
apres soumission d'une proposition a demontrer, genere 5 listes*/
tri_Abox([],[],[],[],[],[]).

tri_Abox([(Instance, some(Role,Concept))|Abi_suite],Lie,Lpt,Li,Lu,Ls) :-  
                                                    concat([(Instance, some(Role,Concept))],Lie_suite,Lie),
                                                    tri_Abox(Abi_suite,Lie_suite,Lpt,Li,Lu,Ls), !.

tri_Abox([(Instance, all(Role,Concept))|Abi_suite],Lie,Lpt,Li,Lu,Ls) :-
                                                    concat([(Instance, all(Role,Concept))],Lpt_suite,Lpt),
                                                    tri_Abox(Abi_suite,Lie,Lpt_suite,Li,Lu,Ls),!.

tri_Abox([(Instance, and(Concept1,Concept2))|Abi_suite],Lie,Lpt,Li,Lu,Ls) :-
                                                    concat([(Instance, and(Concept1,Concept2))],Li_suite,Li),
                                                    tri_Abox(Abi_suite,Lie,Lpt,Li_suite,Lu,Ls), !.


tri_Abox([(Instance, or(Concept1,Concept2))|Abi_suite],Lie,Lpt,Li,Lu,Ls) :-  
                                                    concat([(Instance, or(Concept1,Concept2))],Lu_suite,Lu),
                                                    tri_Abox(Abi_suite,Lie,Lpt,Li,Lu_suite,Ls), !.

tri_Abox([(Instance, Concept)|Abi_suite],Lie,Lpt,Li,Lu,Ls) :-
                                                    concat([(Instance, Concept)],Ls_suite,Ls),
                                                    tri_Abox(Abi_suite,Lie,Lpt,Li,Lu,Ls_suite),!.
                                                    
tri_Abox([(Instance, not(Concept))|Abi_suite],Lie,Lpt,Li,Lu,Ls) :- 
                                                    concat([(Instance, not(Concept))],Ls_suite,Ls),
                                                    tri_Abox(Abi_suite,Lie,Lpt,Li,Lu,Ls_suite),!.

/*not_clash: verifie qu'une Abox ne contient pas de clash*/
not_clash([]).
not_clash([(Instance, Concept)|Abox_suite]):- nnf(not(Concept),Not_Concept),
                                            /*verifier que I: C et I: ¬C ne sont pas dans une meme ABox*/
                                            not(member((Instance,Not_Concept),Abox_suite)),
                                            not_clash(Abox_suite).

/* resolution : deroule le methode des tableaux semantiques*/
resolution(Lie, Lpt, Li, Lu, Ls, Abr) :- Lie\==[],not_clash(Ls),complete_some(Lie, Lpt, Li, Lu, Ls, Abr).
resolution([], Lpt, Li, Lu, Ls, Abr) :- Li\==[], not_clash(Ls), transformation_and([], Lpt, Li, Lu, Ls, Abr).
resolution([], Lpt, [], Lu, Ls, Abr) :- Lpt\==[], not_clash(Ls), deduction_all([], Lpt, [], Lu, Ls, Abr).
resolution([], [], [], Lu, Ls, Abr) :- Lu\==[], not_clash(Ls),transformation_or([], [], [], Lu, Ls, Abr).

resolution([], [], [], [], Ls, Abr) :-  not(not_clash(Ls)),!.
/*resolution est a true : Si toutes les branches de l'arbre de resolution sont fermees, 
ainsi, on peut dire que Abe est insatisfiable et l'on peut donc affirmer que la proposition initiale est demontree*/


/*traiter le cas ou l'assertion qu'on veut ajouter est deja presente dans la liste qu'on veut mettre a jour : la liste reste inchange*/
evolue((I, some(R,C)), Lie, Lpt, Li, Lu, Ls, Lie, Lpt, Li, Lu, Ls) :- member((I, some(R,C)), Lie).
/*traiter le cas ou l'assertion qu'on veut ajouter n'est pas dans la liste qu'on veut mettre a jour*/
evolue((I, some(R,C)), Lie, Lpt, Li, Lu, Ls, Lie1, Lpt, Li, Lu, Ls) :- not(member((I, some(R,C)), Lie)),
                                                                            /*ajouter (I, some(R,I)) a Lie de sorte a avoir Lie1 qui est sa version mise a jour donc Lie=Lie1*/
                                                                           concat([(I, some(R,C))],Lie, Lie1).
                                                                           

evolue((I,and(C1,C2)), Lie, Lpt, Li, Lu, Ls, Lie, Lpt, Li, Lu, Ls):- member((I,and(C1,C2)),Li).
evolue((I,and(C1,C2)), Lie, Lpt, Li, Lu, Ls, Lie, Lpt, Li1, Lu, Ls):-not(member((I,and(C1,C2)),Li)),concat([(I,and(C1,C2))], Li, Li1).

evolue((I,or(C1,C2)), Lie, Lpt, Li, Lu, Ls, Lie, Lpt, Li, Lu, Ls):- member((I,or(C1,C2)),Lu).
evolue((I,or(C1,C2)), Lie, Lpt, Li, Lu, Ls, Lie, Lpt, Li, Lu1, Ls):-not( member((I,or(C1,C2)),Lu)),concat([(I,or(C1,C2))],Lu,Lu1).

evolue((I,all(R,C)), Lie, Lpt, Li, Lu, Ls, Lie, Lpt, Li, Lu, Ls):- member((I,all(R,C)),Lpt).
evolue((I,all(R,C)), Lie, Lpt, Li, Lu, Ls, Lie, Lpt1, Li, Lu, Ls):- not(member((I,all(R,C)),Lpt)),concat([(I,all(R,C))],Lpt,Lpt1).

evolue((I,C), Lie, Lpt, Li, Lu, Ls, Lie, Lpt, Li, Lu, Ls):- member((I,C),Ls).
evolue((I,C), Lie, Lpt, Li, Lu, Ls, Lie, Lpt, Li, Lu, Ls1):- not(member((I,C),Ls)), concat([(I,C)],Ls,Ls1).

/*evolue_L: permet d'ajouter une liste d'assertions de concept a une liste LX, sa version mise a jour est LX1*/
evolue_L([], Lie, Lpt, Li, Lu, Ls, Lie, Lpt, Li, Lu, Ls).
evolue_L([X|L], Lie, Lpt, Li, Lu, Ls, Lie1, Lpt1, Li1, Lu1, Ls1) :- evolue(X, Lie, Lpt, Li, Lu, Ls, Lie_, Lpt_, Li_, Lu_, Ls_), 
                                                                    evolue_L(L, Lie_, Lpt_, Li_, Lu_, Ls_, Lie1, Lpt1, Li1, Lu1, Ls1).


transformation_and(Lie, Lpt, [(I, and(C1, C2))|Li_suite], Lu, Ls, Abr) :- 
                                                                        /*ajouter I:C1 et I:C2 a Ls, le resultat est dans Ls1
                                                                        Note: on travaille sur Li_suite afin de supprimer la formule (I, and(C1, C2) (etant justement traitee)*/
                                                                        evolue_L([(I,C1),(I,C2)], Lie, Lpt, Li_suite, Lu, Ls, Lie1, Lpt1, Li1, Lu1, Ls1),nl,
                                                                        affiche_evolution_Abox(Ls, Lie, Lpt, [(I,and(C1,C2))|Li_suite], Lu, Abr, Ls1, Lie1, Lpt1, Li1, Lu1, Abr),
                                                                        resolution(Lie1,Lpt1,Li1,Lu1,Ls1,Abr).


transformation_or(Lie, Lpt, Li, [(I, or(C1, C2))|Lu_suite], Ls, Abr) :- 
                                                                        /*Creer premier noeud : ajouter I:C1 au noeud en cours de traitement*/
                                                                        evolue((I,C1), Lie, Lpt, Li, Lu_suite, Ls, Lie1, Lpt1, Li1, Lu1, Ls1),nl,
                                                                        affiche_evolution_Abox(Ls, Lie, Lpt, Li, [(I,or(C1,C2))|Lu_suite], Abr, Ls1, Lie1, Lpt1, Li1, Lu1, Abr),
                                                                        resolution(Lie1,Lpt1,Li1,Lu1,Ls1,Abr),
                                                                        write("APPLICATION TRANSFORMATION OR => SEPARATION DANS L'ARBORESCENCE"),nl,
                                                                        /*Creer deuxieme noeud : ajouter I:C2 au noeud en cours de traitement*/
                                                                        evolue((I,C2),Lie, Lpt, Li, Lu_suite, Ls, Lie2, Lpt2, Li2, Lu2, Ls2),nl,
                                                                        affiche_evolution_Abox(Ls, Lie, Lpt, Li, [(I,or(C1,C2))|Lu_suite], Abr, Ls2, Lie2, Lpt2, Li2, Lu2, Abr),
                                                                        resolution(Lie2,Lpt2,Li2,Lu2,Ls2,Abr).                                                                
                                                                                                            
complete_some([(I, some(R,C))|Lie_suite], Lpt,Li,Lu,Ls,Abr) :-  genere(I2), 
                                                                /*ajouter l'instance precedement cree a Ls de sorte a ce que Ls1 contiene I2:C, 
                                                                Note: on travail sur Lie_suite afin de supprimer la formule (I, some(R,C) (etant justement traitee)*/
                                                                evolue((I2,C), Lie_suite, Lpt,Li,Lu,Ls, Lie1,Lpt1,Li1,Lu1,Ls1),
                                                                /*ajouter <I1,I2>:R a Abr, le resultat est Abr1*/
                                                                concat([(I,I2,R)], Abr, Abr1),nl,
                                                                affiche_evolution_Abox(Ls, [(I,some(R,C))|Lie_suite], Lpt,Li,Lu,Abr, Ls1,Lie1,Lpt1,Li1,Lu1, Abr1),!,
                                                                resolution(Lie1,Lpt1,Li1,Lu1,Ls1,Abr1).


deduction_all(Lie, [(I, all(R, C))|Lpt_suite], Li, Lu, Ls, Abr) :-
                                                                    setof((I2,C), member((I,I2,R), Abr), L),
                                                                    /*L doit contenir toutes les assertions d'instances (I2,C) tel que pour toute instance I2, elle est en relation R avec I, soit les <I,I2>:R dans Abr*/
                                                                    evolue_L(L, Lie, Lpt_suite, Li, Lu, Ls, Lie1, Lpt1, Li1, Lu1, Ls1),nl,
                                                                    /*ajouter les assertions d'instances (I2,C) precedement sauvegardees au noeud en cours de traitement*/
                                                                    affiche_evolution_Abox(Ls, Lie, [(I, all(R, C))|Lpt_suite], Li, Lu, Abr, Ls1, Lie1, Lpt1, Li1, Lu1, Abr),
                                                                    resolution(Lie1,Lpt1,Li1,Lu1,Ls1,Abr).

/*afficher C que s'il est atomique (condition en principe verifiee car la Abox est sense etre simplifiee et mise sous nnf)*/
affiche_C(C) :- cnamea(C), write(C), !. 
affiche_C(not(C)) :- write(' \u00AC'), affiche_C(C), !.
affiche_C(and(C1, C2)) :- affiche_C(C1), write(' & '), affiche_C(C2), !.
affiche_C(or(C1, C2)) :- affiche_C(C1), write(' \u2294 '), affiche_C(C2), !.
affiche_C(some(R, C)) :- role(R), write(' E '), write(R), write('.'), affiche_C(C), !.
affiche_C(all(R, C)) :- role(R), write(' \u2200'), write(R), write('.'), affiche_C(C), !.


affiche_Abe([]).
affiche_Abe([(I,C)|L]) :- write(I), write(":"), affiche_C(C),nl,affiche_Abe(L), !.

affiche_Abr([]).
affiche_Abr([(I,I2, R)|L]) :- write("<"), write(I), write(","),write(I2),write(">"),write(":"),write(R),nl, affiche_Abr(L), !.



affiche_evolution_Abox(Ls1, Lie1, Lpt1, Li1, Lu1, Abr1, Ls2, Lie2, Lpt2, Li2, Lu2, Abr2) :-
                    write("_______________________________________"),
                    write("|            Etat de depart           |"),
                    write("_______________________________________"),nl,nl,

                    affiche_Abe(Ls1),
                    affiche_Abe(Lie1),
                    affiche_Abe(Lpt1),
                    affiche_Abe(Li1),
                    affiche_Abe(Lu1),nl,
                    affiche_Abr(Abr1),

                    nl,nl,nl,

                    write("_______________________________________"),
                    write("|            Etat d'arrivee           |"),
                    write("_______________________________________"),nl,nl,
                    affiche_Abe(Ls2),
                    affiche_Abe(Lie2),
                    affiche_Abe(Lpt2),
                    affiche_Abe(Li2),
                    affiche_Abe(Lu2),nl,
                    affiche_Abr(Abr2).
/*
######################################################################
#                                                                    #
#             EXECUTION DU PROGRAMME                                 #
#                                                                    #
#######################################################################
*/

programme :-nl,nl,
            write("-------- PARTIE 1 ---------"),nl, nl,
            premiere_etape(TBox, Abi, Abr),
            write("-------- PARTIE 2 ---------"),nl, nl,
            deuxieme_etape(Abi, Abi1, TBox),
            write("-------- PARTIE 3 ---------"),nl, nl,
            troisieme_etape(Abi1, Abr).


