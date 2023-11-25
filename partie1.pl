/*1.---------------------------- Verification de la correction semantique ----------------------------*/


/*Semantique est a vrai si elle verifie que tout identificateur de concept, d'instance, de role en est bien un et qu'ils sont uniques */
semantique() :- setof(Ca, cnamea(Ca), ListeConceptsAtomiques),
                setof(Cna, cnamena(Cna), ListeConceptsNonAtomiques),
                setof(R, rname(R), ListeRoles),
                setof(I, iname(I), ListeInstances),
                append(ListeConceptsAtomiques, ListeConceptsNonAtomiques, L1),
                append(ListeRoles, ListeInstances, L2),
                append(L1, L2, L), 
                unique(L).


/* Verifier le cas de base la liste vide est unique ou qu'on test sur un seul element*/
unique([]).
/*sinon, faire unique(X|[])*/
unique([X]).
/* Verifier l'unicite des elements pour la tete de la liste*/
unique([X | L]) :-
    /* Verifier que X n'est pas dans L*/
    \+ member(X, L), 
    /*reccursion*/
    unique(L).


/*2.---------------------------- Verification syntaxique ----------------------------*/


/*---- Concepts atomiques et non atomiques ----*/
/*Un concept est valide que s'il est atomique ou non atomique*/
concept(X) :- cnamea(X).
concept(X) :- cnamena(X).
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
concept(not(C)) :- concept(C).
concept(and(C1, C2)) :- concept(C1), concept(C2).
concept(or(C1, C2)) :- concept(C1), concept(C2).
concept(some(R, C)) :- role(R), concept(C).
concept(all(R, C)) :- role(R), concept(C).


/*---- Verification syntaxique de la TBox et ABox ----*/

/*Construction des listes de TBox et ABox*/
/*TBox contient les definitions
Notons que dans Tbox on a ne represente pas de relations de subsumption par souci de simplification (enoncé)*/
listeTBox(TBox) :- setof((Concept_g, Concept_d), equiv(Concept_g, Concept_d), TBox).
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

/**Cas2 : ABoxRole contient les assertions de roles*/
verifierInstR(Instance1, Instance2, Role) :- instance(Instance1), instance(Instance2), role(Role).
/*Cas de base ou la ABox est vide*/
syntaxeABoxRole([]).
/*Verifier que chaque element de la ABoxRole est une assertion de role valide */
syntaxeABoxRole([(Instance1, Instance2, Role)] | L) :- verifierInstR(Instance1, Instance2, Role), 
                                                        syntaxeABoxRole(L).

/*Il faut que les 2 cas soient verifies*/
syntaxeABox(ABoxConcept, ABoxRole) :- syntaxeABoxConcept(ABoxConcept), syntaxeABoxRole(ABoxRole).

/*--- Verifier la syntaxe de TBox ---*/

verifierEquiv(Concept_g, Concept_d) :- cnamena(Concept_g), concept(Concept_d).
/*Cas de base ou la TBox est vide*/
syntaxeTBox([]).
/*Verifier que chaque element de la TBox est une equivalence (definition) valide */
syntaxeTBox([(Concept_g, Concept_d) | L]) :- verifierEquiv(Concept_g, Concept_d), SyntaxeTBox(L).

/*--- Verifier la syntaxe generale ---*/
syntaxe(TBox, ABoxConcept, ABoxRole) :- syntaxeTBox(TBox), syntaxeABox(ABoxConcept, ABoxRole).
