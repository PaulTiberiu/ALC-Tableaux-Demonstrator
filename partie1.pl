
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
unique(X | []).
/* Verifier l'unicite des elements pour la tete de la liste*/
unique([X | L]) :-
    /* Verifier que X n'est pas dans L*/
    \+ member(X, L), 
    /*reccursion*/
    unique(L).


/*2.---------------------------- Verification syntaxique ----------------------------*/



/*---- Concepts atomiques et non atomiques ----*/
/*Un concept est valide que s'il est atomique ou non atomique*/
syntaxeConcept(X) :- cnamea(X).
syntaxeConcept(X) :- cnamena(X).
/*Ajouter les identificateurs anything et nothing qui correspondent respectivement a ⊤ et ⊥*/
cnamea(X) :- nothing(X).
cnamea(X) :- anything(X).

/*Instances*/
/*Une instance I est valide que s'il existe un identificateur dinstance associe a cette instance*/
instance(I) :- iname(I).

/*Role*/
/*Un role R est valide que s'il existe un identificateur de role associe a ce role*/
role(R) :- rname(R).

/*Grammaire*/
syntaxeConcept(not(C)) :- syntaxeConcept(C).
syntaxeConcept(and(C1, C2)) :- syntaxeConcept(C1), syntaxeConcept(C2).
syntaxeConcept(or(C1, C2)) :- syntaxeConcept(C1), syntaxeConcept(C2).
syntaxeConcept(some(R, C)) :- role(R), syntaxeConcept(C).
syntaxeConcept(all(R, C)) :- role(R), syntaxeConcept(C).




/*---- Verification syntaxique de la TBox et ABox ----*/

/*Construction des listes de TBox et ABox*/
/*TBox contient les definitions
Notons que dans Tbox on a ne represente pas de relations de subsumption par souci de simplification (enoncé)*/
listeTBox(TBox) :- setof((Concept_g, Def), equiv(Concept_g, Def), TBox).
/*ABoxCon contient les assertions de concepts*/
listeABoxConcept(ABoxConcept) :- setof((Instance, Concept), inst(Instance, Concept), ABoxConcept).
/*ABoxRole contient les assertions de roles*/
listeABoxRole(ABoxRole) :- setof((Instance1, Instance2, Role), instR(Instance1, Instance2, Role), ABoxRole).





/*--- Verifier la syntaxe de ABox ---*/

/**Cas1 : ABoxConcept contient les assertions de concepts*/
verifierInst(Instance, Concept) :- instance(Instance), cnamena(Concept).
verifierInst(Instance, Concept) :- instance(Instance), cnamea(Concept).
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
syntaxeABoxRole([(Instance1, Instance2, Role)] | L) :- verifierInstR(Instance1, Instance2, Role), 
                                                        syntaxeABoxRole(L).

/*Il faut que les 2 cas soient verifies*/
syntaxeABox(ABoxConcept, ABoxRole) :- syntaxeABoxConcept(ABoxConcept), syntaxeABoxRole(ABoxRole).





/*--- Verifier la syntaxe de TBox ---*/

verifierEquiv(Concept_g, Def) :- cnamena(Concept_g), syntaxeConcept(Def).
/*Cas de base ou la TBox est vide*/
syntaxeTBox([]).
/*Verifier que chaque element de la TBox est une equivalence (definition) valide */
syntaxeTBox([(Concept_g, Def) | L]) :- verifierEquiv(Concept_g, Def), syntaxeTBox(L).




/*--- Verifier la syntaxe generale ---*/

syntaxe(TBox, ABoxConcept, ABoxRole) :- syntaxeTBox(TBox), syntaxeABox(ABoxConcept, ABoxRole).


/*-------------------- concept : Verification de la correction semantique de la correction syntxique --------------------*/
/*concept est a true si la semantique est correcte et que la syntaxe aussi*/
concept :- semantique,
            listeTBox(TBox),
            listeABoxConcept(ABoxConcept),
            listeABoxRole(ABoxRole),
            syntaxe(TBox, ABoxConcept, ABoxRole).


/*3.---------------------------- Verification l'autoreference ----------------------------*/

/*Cas ou la definition est un concept atomique: rien à verifier on est sur qu'il n'y a pas de cycle*/
pasAutoRef_element(Concept, Def) :- cnamea(Def). 

/*Cas ou la definition est un concept non atomique: 1. verifier qu'il n'est pas unifiable avec le concept gauche et 2. recuperer la definition de la definition puis 3. 
Appliquer la recursivite pour s'assurer qu'il n'y a pas de cycle en partant cette fois de la definition de la definition*/
/***** test : /= OU BIEN /== */
pasAutoRef_element(Concept, Def) :- cnamena(Def), Concept \= Def, equiv(Def, Def2), pasAutoRef_element(Concept, Def2).

/*Traiter les differents cas possibles de Def (definition d'un concept)*/
pasAutoRef_element(Concept, and(Def1, Def2)) :- pasAutoRef_element(Concept, Def1), pasAutoRef_element(Concept, Def2).
pasAutoRef_element(Concept, or(Def1, Def2)) :- pasAutoRef_element(Concept, Def1), pasAutoRef_element(Concept, Def2).
pasAutoRef_element(Concept, not(Def1)) :- pasAutoRef_element(Concept, Def1).
pasAutoRef_element(Concept, some(R, C)) :- pasAutoRef_element(Concept, C).
pasAutoRef_element(Concept, all(R, C)) :- pasAutoRef_element(Concept, C).

/*Cas de base*/
pasAutoRef_list([]). 
/*Cas general : prend en entree la TBox sous forme de liste*/
pasAutoRef_list([(Concept, Def)| L]) :- pasAutoRef_element(Concept, Def), pasAutoRef_list(L). 
/*Note : avoir un (Concept, Def) dans la liste de la TBox signifie Concept equivalent a Def*/



/*-------------------- pas_autoref : Verification generale de l'autoreference --------------------*/

/*Verification de l'existance d'une auto-reference (d'un cycle) dans le fichier fourni*/
/*test : N'OUBLIER PAS D'AJOUTER DES WRITE POUR VOIR LE RESULTAT DANS LE TERMINAL*/
pas_autoref :- listeTBox(TBox), pasAutoRef_list(TBox).
/*pasAutoRef_fichier() :- listeTBox(TBox), pasAutoRef_list(TBox)...--------------------------------------------------------------------*/




/*4.---------------------------- Traitement TBox ----------------------------*/

/*remplacer(...) a pour objectif de remplacer par une expression ou ne figurent plus que des identificateurs de concepts atomiques*/
/* deroulement remplacer(...) :
femme = x et Y
z = femme et w

remplacer(z, Valeur)
remplacer(femme, def1)
def1=x et Y
remplacer(w, def2)
def2=w
Valeur = and(def1, def2) = x et Y et w
*/

/*Cas ou Concept est atomique : ne rien faire c'est a dire le remplacer par lui meme */ 
remplacer(Concept, Concept) :- cnamea(Concept).

/*Cas ou Concept est non atomique : recuperer Def2 (sa definition) est appliquer une recursivite dessus de sorte a etre sur que Def2 peut en effet etre remplace par Def */ 
remplacer(Concept, Def) :- cnamena(Concept), equiv(Concept, Def2), remplacer(Def2, Def).

/*Traiter les differents cas possibles de remplacer(Def2, Def)*/
remplacer(not(Concept), not(Def)) :- remplacer(Concept, Def).
remplacer(and(Concept1, Concept2), and(Def1, Def2)) :- remplacer(Concept1, Def1), remplacer(Concept2, Def2).
remplacer(or(Concept1, Concept2), or(Def1, Def2)) :- remplacer(Concept1, Def1), remplacer(Concept2, Def2).
remplacer(all(Role1, Concept), all(Role2,Def)) :- Role1 == Role2, remplacer(Concept,Def). 
remplacer(some(Role1, Concept), some(Role2,Def)) :- Role1 == Role2, remplacer(Concept,Def). 

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
traitement_TBox(nnf_TBox) :- listeTBox(TBox), remplacer_liste_TBox(TBox, nnf_TBox).



/*5 .---------------------------- Traitement ABox ----------------------------*/

/* --- Verifier si un concept (definit pour une certaine instance dans la ABox) est dans la TBox finale (simplifiee et mise sous nnf) --- */
/*Cas ou le concept est en tete de liste de la TBox*/
verifier_concept_dans_TBox(Concept, Def, [(C1, Def1) | L] ) :- Concept = C1, Def = Def1.
/*Cas ou le concept n'est pas en tete de liste de la TBox, soit appliquer une recursiviter sur les elements restants de la liste */
verifier_concept_dans_TBox(Concept, Def, [(C1, Def1) | L] ) :- Concept \= C1, Def = Def1, verifier_concept_dans_TBox(Concept, Def, L).
/*Note : verifier_concept_dans_TBox retourne true si Def est bien la definition simplifiee est mise sous forme normale negative de Concept, qu'on retrouve dans nnf_TBox*/


/*Cas de base*/
remplacer_liste_ABox([], []).

/*Cas ou le concept d'une instance de la ABox est atomique : (ne rien faire) passer au prochain element de la liste ABox*/
remplacer_liste_ABox([(Inst, Concept) | L1], [(Inst, Concept) | L2]) :- cnamea(Concept), remplacer_liste_ABox(L1, L2).

/*Cas ou le concept d'une instance de la ABox est non atomique : 
remplacer Concept par Def qui est sa definition simplifiee et mise sous nnf (qu'on recuperer à partir de la TBox traitee) 
puis passer au prochain element de la liste ABox*/
remplacer_liste_ABox([(Inst, Concept) | L1], [(Inst, Def) | L2]) :- cnamena(Concept), 
                                                                    traitement_TBox(nnf_TBox),
                                                                    verifier_concept_dans_TBox(Concept, Def, nnf_TBox),
                                                                    remplacer_liste_ABox(L1, L2).

/*traitement_ABox retourne true si elle est appliquee a la ABox ecrite sous forme normale negative*/
traitement_ABox(nnf_ABox) :- listeABoxConcept(ABoxConcept),  remplacer_liste_ABox(ABoxConcept, nnf_ABox).
/*Note : pour verifier la coherence d'une ABox il est inutile de traiter le cas des assertions de roles car un role ne peut etre ni simplifie ni mis sous nnf*/

/*-------------------- partie1 : Verification de la coherence de toute la premiere partie --------------------*/


premiere_etape(TBox, Abi, Abr) :-  (concept, write("La correction semantique et syntaxique sont verifiees"), nl; nl,
                                            write("La correction semantique et syntaxique ne sont pas verifiees"), nl, fail).


/*
premiere_etape(TBox, Abi, Abr) :-  (concept, write("La correction semantique et syntaxique sont verifiees"), nl; nl,
                                            write("La correction semantique et syntaxique ne sont pas verifiees"), nl, fail),
                                            (pas_autoref, write("Il n'y a pas des definitions des concepts circulaires"), nl; nl,
                                            write("Il existe au moins une definition de concept circulaire"), nl, fail),
                                            traitement_TBox(TBox),
                                            traitement_ABox(Abi),
                                            listeABoxRole(Abr).
*/
/*
premiere_etape(TBox, Abi, Abr) :- concept(),
                                pas_autoref(),
                                traitement_TBox(TBox),
                                traitement_ABox(Abi),
                                listeABoxRole(Abr).
*/
