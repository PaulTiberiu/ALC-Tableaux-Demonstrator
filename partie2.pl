deuxieme_etape(Abi,Abi1,Tbox) :- saisie_et_traitement_prop_a_demontrer(Abi,Abi1,Tbox).

saisie_et_traitement_prop_a_demontrer(Abi,Abi1,Tbox) :-
    nl,write('Entrez le numero du type de proposition que vous voulez demontrer :'),nl,
    write('1 Une instance donnee appartient a un concept donne.'),nl,
    write('2 Deux concepts n"ont pas d"elements en commun(ils ont une intersection vide).'),nl, 
    read(R), 
    suite(R,Abi,Abi1,Tbox).

suite(1,Abi,Abi1,Tbox) :- acquisition_prop_type1(Abi,Abi1,Tbox),!.

suite(2,Abi,Abi1,Tbox) :- acquisition_prop_type2(Abi,Abi1,Tbox),!.

suite(R,Abi,Abi1,Tbox) :- nl,write('Cette reponse est incorrecte.'),nl,
                          saisie_et_traitement_prop_a_demontrer(Abi,Abi1,Tbox).


/*--------------Acquisition d'une proposition de type 1--------------*/
get_prop_type1(Instance, Concept) :- write("--Traiter une proposition de type1--")
                                    write("Veuillez introduire l'identificateur de l'instance :"), nl, read(Instance),
                                    write("Veuillez introduire l'identificateur du concept ou sa definition :"), nl, read(Concept),
                                    /*afficher une erreur si les informations entrees par l'utilisateur sont syntaxiquement incorrects*/
                                    (verifierInst(Instance, Concept);
                                    write("Error : syntaxe de la ABox non respectee, l'instance ou le concept introduit n'est pas defini"),nl, fail)

/*Simplifier Concept, recuperer sa negation et mettre sous nnf*/
traitement_prop_type1((Instance, Concept), (Instance, new_Concept)):- remplacer(not(Concept), not_Concept_simplifie ),
                                                                        nnf(not_Concept_simplifie, new_Concept).
/*Note : le resultat de cette etape est de construire un nouveau element (Instance, new_Concept) pour lequel new_Concept est la negation de Concept simplifié qu'on met sous nnf*/

acquisition_prop_type1(Abi,Abi1,Tbox) :- get_prop_type1(Instance, Concept),
                                         traitement_prop_type1((Instance, Concept), (Instance, new_Concept)),
                                         /*ajouter (Instance, new_Concept) a la ABox*/
                                         concat(Abi,[(Instance, new_Concept)], Abi1).

/*--------------Acquisition d'une proposition de type 2--------------*/
get_prop_type2(Concept1, Concept2) :- write("--Traiter une proposition de type2--")
                                    write("Veuillez introduire l'identificateur du premier concept ou sa definition :"), nl, read(Concept1),
                                    write("Veuillez introduire l'identificateur du deuxieme concept ou sa definition :"), nl, read(Concept2),
                                    /*afficher une erreur si les informations entrees par l'utilisateur sont syntaxiquement incorrects*/
                                    (syntaxeConcept(and(Concept1, Concept2));
                                    write("Error : syntaxe de la ABox non respectee, au moins un des deux concepts introduits n'est pas defini"),nl, fail)

/*Simplifier les deux concepts, recuperer la negation et mettre sous nnf*/
traitement_prop_type2(and(Concept1, Concept2), (Instance, (new_Concept1, new_Concept2))):- remplacer(Concept1, Concept1_simplifie ),
                                                                                        remplacer(Concept2, Concept2_simplifie ),
                                                                                        nnf(Concept1_simplifie, new_Concept1),
                                                                                        nnf(Concept2_simplifie, new_Concept2).
/*Note : le resultat de cette etape est de creer une nouvelle instance qui est une conjonction des deux nouveaux concepts resultant de la simplification et la mise sous nnf des concepts introduits par le user*/

acquisition_prop_type2(Abi,Abi1,Tbox) :- get_prop_type2(Concept1, Concept2),
                                         traitement_prop_type2(and(Concept1, Concept2), (Instance, (new_Concept1, new_Concept2))),
                                         /*ajouter (Instance, (new_Concept1, new_Concept2)) a la ABox*/
                                         concat(Abi,[(Instance, (new_Concept1, new_Concept2))], Abi1).
