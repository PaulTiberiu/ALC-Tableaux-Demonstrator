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

/*donner une auto-reference
rname(creePar).
cnamena(sculpture). il faut passer sculpture en non atomique
equiv(sculpture,and(objet,all(creePar,sculpteur))).
*/


/*ABox*/

/*Predicats pour les instantiations de concepts*/
inst(michelAnge,personne).
inst(david,sculpture).
inst(sonnets,livre).
inst(vinci,personne).
inst(joconde,objet).
/*
inst(tibi,personne).
avec ca, syntaxe ABox n'est pas verifie car on n'a pas declare tibi
inst(david,etudiant).
pareil, mais on n'a pas declare etudiant
*/

/*Predicats pour les instantiations de roles*/
instR(michelAnge, david, aCree).
instR(michelAnge, sonnets, aEcrit).
instR(vinci, joconde, aCree).
