/*1. Verification de la correction semantique*/

/**a ecrire dans la console pour pouvoir verifier (pas demande mais bon)?----a voir plus tard----**/
semantique(X) :- setof(X, cnamea(X), ListeConceptsAtomiques).
semantique(X) :- setof(X, cnamena(X), ListeConceptsNonAtomiques).
semantique(X) :- setof(X, iname(X), ListeInstances).
semantique(X) :- setof(X, rname(X), ListeRoles).

/*2. Verification syntaxique*/

/*concepts atomiques et non atomiques*/
concept(X) :- cnamea(X). /**un concept est valide que si il est atomique ou non atomique**/
concept(X) :- cnamena(X).

/*instances */
instance(I) :- iname(I). /** une instance I est valide que si il existe un identificateur d'instance associé à cette instance **/

/*role*/
role(R) :- rname(R). /** un role R est valide que si il existe un identificateur de role associé à ce role **/


/*Grammaire*/
concept(not(C)) :- concept(C).
concept(and(C1, C2)) :- concept(C1), concept(C2).
concept(or(C1, C2)) :- concept(C1), concept(C2).
concept(some(R, C)) :- role(R), concept(C).
concept(all(R, C)) :- role(R), concept(C).


