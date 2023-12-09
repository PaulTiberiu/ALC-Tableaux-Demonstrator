troisieme_etape(Abi,Abr) :- tri_Abox(Abi,Lie,Lpt,Li,Lu,Ls),
                            resolution(Lie,Lpt,Li,Lu,Ls,Abr),
                            nl,write('Youpiiiiii, on a demontre la proposition initiale !!!').

/*tri_Abox : A partir de la liste des assertions de concepts de la Abox etendue 
apres soumission d'une proposition a demontrer, genere 5 listes*/

tri_Abox([],[],[],[],[],[]).
/*a tester egalement AVEC signe d'exclamation pour voir ce que ca donne*/
tri_Abox([X|Abi_suite],[X|Lie_suite],Lpt,Li,Lu,Ls) :- X=(Instance, some(Role,Concept)), 
                                                    instance(Instance),
                                                    syntaxeConcept(some(Role,Concept)),
                                                    traitement_ABox([X|Abi_suite]),
                                                    tri_Abox(Abi_suite,Lie_suite,Lpt,Li,Lu,Ls).

tri_Abox([X|Abi_suite],Lie,[X|Lpt_suite],Li,Lu,Ls) :- X=(Instance, all(Role,Concept)), 
                                                    instance(Instance), 
                                                    syntaxeConcept(all(Role, Concept)),
                                                    traitement_ABox([X|Abi_suite]),
                                                    tri_Abox(Abi_suite,Lie,Lpt_suite,Li,Lu,Ls).

tri_Abox([X|Abi_suite],Lie,Lpt,[X|Li_suite],Lu,Ls) :-X=(Instance, and(Concept1,Concept2)),
                                                    instance(Instance),
                                                    syntaxeConcept(and(Concept1,Concept2)),
                                                    traitement_ABox([X|Abi_suite]),
                                                    tri_Abox(Abi_suite,Lie,Lpt,Li_suite,Lu,Ls).
                                                    /*write("on est dans triAbox and"),nl.*/

tri_Abox([X|Abi_suite],Lie,Lpt,Li,[X|Lu_suite],Ls) :- X=(Instance, or(Concept1,Concept2)), 
                                                    instance(Instance), 
                                                    syntaxeConcept(or(Concept1,Concept2)),
                                                    traitement_ABox([X|Abi_suite]),
                                                    tri_Abox(Abi_suite,Lie,Lpt,Li,Lu_suite,Ls).

tri_Abox([X|Abi_suite],Lie,Lpt,Li,Lu,[X|Ls_suite]) :- X=(Instance, Concept), 
                                                    instance(Instance), 
                                                    syntaxeConcept(Concept),
                                                    traitement_ABox([X|Abi_suite]),
                                                    tri_Abox(Abi_suite,Lie,Lpt,Li,Lu,Ls_suite).
                                                    /*write("on est dans triAbox s"),nl. et on va tester avec michelAnge, personne*/
                                                    
tri_Abox([X|Abi_suite],Lie,Lpt,Li,Lu,[X|Ls_suite]) :- X=(Instance, not(Concept)), 
                                                    instance(Instance), 
                                                    syntaxeConcept(not(Concept)), 
                                                    traitement_ABox([X|Abi_suite]),
                                                    tri_Abox(Abi_suite,Lie,Lpt,Li,Lu,Ls_suite).
/*Note : 
- ajouter la verification des instances et de la syntaxe des concepts pour s'assurer que tous tes coherent
- ajouter traitement_ABox(Abi) pour s'assurer que la Abox donnee en parametre est bien simplifiee et mise sous nnf*/

/*not_clash: verifie qu'une Abox ne contient pas de clash*/
not_clash([X|Abox_suite]):- X=(Instance, Concept),
                            /*ajouter traitement_ABox pour etre sur de comparer not(C) mis sous nnf a des elements d'une ABox mis sous nnf et simplifies*/
                            traitement_ABox([X|Abi_suite]), 
                            nnf(not(Concept),not_Concept),
                            /*verifier que I: C et I: ¬C ne sont pas dans une meme ABox*/
                            not(member((Instance,not_Concept),Abox_suite)),
                            not_clash(Abox_suite).

/* resolution : deroule le methode des tableaux semantique*/
resolution(Lie, Lpt, Li, Lu, Ls, Abr) :- Lie\==[], not_clash(Ls), complete_some(Lie, Lpt, Li, Lu, Ls, Abr).
resolution([], Lpt, Li, Lu, Ls, Abr) :- Li\==[], not_clash(Ls), transformation_and([], Lpt, Li, Lu, Ls, Abr).
resolution([], Lpt, [], Lu, Ls, Abr) :- Lpt\==[], not_clash(Ls), deduction_all([], Lpt, [], Lu, Ls, Abr).
resolution([], [], [], Lu, Ls, Abr) :- Lu\==[], not_clash(Ls), transformation_or([], [], [], Lu, Ls, Abr).
/*A AJOUTER ! pour voir si ca change*/
resolution([], [], [], [], Ls, Abr) :- not(not_clash(Ls)).
/*resolution est a true : Si toutes les branches de l'arbre de resolution sont fermees, 
ainsi, on peut dire que Abe est insatisfiable et l'on peut donc affirmer que la proposition initiale est demontree*/


/*evolue: permet d'ajouter une assertion de concept a une liste LX, sa version mise a jour est LX1*/
/*traiter le cas ou l'assertion qu'on veut ajouter est deja presente dans la liste qu'on veut mettre a jour : la liste reste inchange donc Lie=Lie1*/
evolue((I, some(R,I)), Lie, Lpt, Li, Lu, Ls, Lie1, Lpt1, Li1, Lu1, Ls1) :- member((I, some(R,I)), Lie), Lie1=Lie.
/*traiter le cas ou l'assertion qu'on veut ajouter n'est pas dans la liste qu'on veut mettre a jour*/
evolue((I, some(R,I)), Lie, Lpt, Li, Lu, Ls, Lie1, Lpt1, Li1, Lu1, Ls1) :- not(member((I, some(R,I)), Lie)),
                                                                            /*ajouter (I, some(R,I)) a Lie de sorte a avoir Lie1 qui est sa version mise a jour*/
                                                                           concat(Lie,[(I, some(R,I))], Lie1).

evolue((I, all(R,I)), Lie, Lpt, Li, Lu, Ls, Lie1, Lpt1, Li1, Lu1, Ls1) :- member((I, all(R,I)), Lpt), Lpt1=Lpt.
evolue((I, all(R,I)), Lie, Lpt, Li, Lu, Ls, Lie1, Lpt1, Li1, Lu1, Ls1) :- not(member((I, all(R,I)), Lpt)),
                                                                          concat(Lpt,[(I, all(R,I))], Lpt1).

evolue((I, or(C1,C2)), Lie, Lpt, Li, Lu, Ls, Lie1, Lpt1, Li1, Lu1, Ls1) :- member((I, or(C1,C2)), Lu), Lu1=Lu.
evolue((I, or(C1,C2)), Lie, Lpt, Li, Lu, Ls, Lie1, Lpt1, Li1, Lu1, Ls1) :- not(member((I, or(C1,C2)), Lu)),
                                                                          concat(Lu,[(I, or(C1,C2))], Lu1).
                                                                          
evolue((I, and(C1,C2)), Lie, Lpt, Li, Lu, Ls, Lie1, Lpt1, Li1, Lu1, Ls1) :- member((I, and(C1,C2)), Li), Li1=Li,
evolue((I, and(C1,C2)), Lie, Lpt, Li, Lu, Ls, Lie1, Lpt1, Li1, Lu1, Ls1) :- not(member((I, and(C1,C2)), Li))
                                                                          concat(Li,[(I, and(C1,C2))], Li1).

evolue((I, C), Lie, Lpt, Li, Lu, Ls, Lie1, Lpt1, Li1, Lu1, Ls1) :- member((I, C), Ls), Ls=Ls1.
evolue((I, C), Lie, Lpt, Li, Lu, Ls, Lie1, Lpt1, Li1, Lu1, Ls1) :- not(member((I, C)), Ls),
                                                                   concat(Ls, [(I, C)], Ls1).

/*evolue_L: permet d'ajouter une liste d'assertions de concept a une liste LX, sa version mise a jour est LX1*/
evolue_L([X|L], Lie, Lpt, Li, Lu, Ls, Lie1, Lpt1, Li1, Lu1, Ls1).
evolue_L([X|L], Lie, Lpt, Li, Lu, Ls, Lie1, Lpt1, Li1, Lu1, Ls1) :- evolue(X, Lie, Lpt, Li, Lu, Ls, Lie_, Lpt_, Li_, Lu_, Ls_), 
                                                                      evolue_L(L, Lie_, Lpt_, Li_, Lu_, Ls_, Lie1, Lpt1, Li1, Lu1, Ls1).

/*///tester aussi avec des ! apres affichage*/
transformation_and(Lie, Lpt, [(I, and(C1, C2))|Li_suite], Lu, Ls, Abr) :- 
                                                                        /*ajouter I:C1 et I:C2 au noeud en cours de traitement
                                                                        Note: on travail sur Li_suite afin de supprimer la formule (I, and(C1, C2) (etant justement traitee)*/
                                                                        evolue_L([(I,C1),(I,C2)],Lie, Lpt, Li_suite, Lu, Ls, Lie1, Lpt1, Li1, Lu1, Ls1),
                                                                        /*affiche_evolution_Abox(Ls, Lie, Lpt, [(I,and(C1,C2))|Li_suite], Lu, Abr, Ls1, Lie1, Lpt1, Li1, Lu1, Abr), */
                                                                        resolution(Lie1,Lpt1,Li1,Lu1,Ls1,Abr).

transformation_or(Lie, Lpt, Li, [(I, or(C1, C2))|Lu_suite], Ls, Abr) :- 
                                                                        /*Creer premier noeud : ajouter I:C1 au noeud en cours de traitement*/
                                                                        evolue((I,C1),Lie, Lpt, Li, Lu_suite, Ls, Lie1, Lpt1, Li1, Lu1, Ls1),
                                                                        /*affiche_evolution_Abox(Ls, Lie, Lpt, Li, [(I,or(C1,C2))|Lu_suite], Abr, Ls1, Lie1, Lpt1, Li1, Lu1, Abr),*/ 
                                                                        resolution(Lie1,Lpt1,Li1,Lu1,Ls1,Abr),
                                                                        write("APPLICATION TRANSFORMATION OR"),nl,
                                                                        /*Creer deuxieme noeud : ajouter I:C2 a Lu_suite, le resultat est dans Lu2*/
                                                                        evolue((I,C2),Lie, Lpt, Li, Lu_suite, Ls, Lie2, Lpt2, Li2, Lu2, Ls2),
                                                                        /*affiche_evolution_Abox(Ls, Lie, Lpt, Li, [(I,or(C1,C2))|Lu_suite], Abr, Ls2, Lie2, Lpt2, Li2, Lu2, Abr),*/
                                                                        resolution(Lie2,Lpt2,Li2,Lu2,Ls2,Abr).
/*Note : "transformation_or" est a true si "resolution" appliquee a ses deux noeuds est a true; soit qu'en developpant les deux noeuds on a toutes les feuilles en clash*/                                                               
                                                           
complete_some([(I, some(R,C)|Lie_suite)], Lpt,Li,Lu,Ls,Abr) :- genere(I2), 
                                                                /*ajouter l'instance precedement cree au noeud en cours de traitement, 
                                                                Note: on travail sur Lie_suite afin de supprimer la formule (I, some(R,C) (etant justement traitee)*/
                                                                evolue((I2,C), Lie_suite, Lpt,Li,Lu,Ls, Lie1,Lpt1,Li1,Lu1,Ls1),
                                                                /*ajouter <I1,I2>:R a Abr, le resultat est Abr1*/
                                                                concat(Abr, [(I,I2,R)], Abr1),
                                                                /*affiche_evolution_Abox(Ls, [(I,some(R,C))|Lie_suite], Lpt,Li,Lu,Abr, Ls1,Lie1,Lpt1,Li1,Lu1, Abr1), */
                                                                resolution(Lie1,Lpt1,Li1,Lu1,Ls1,Abr1).


deduction_all(Lie,[(I, all(R,C))|Lpt_suite],Li,Lu,Ls,Abr) :- 
                                        /*L doit contenir toutes les assertions d'instances (I2,C) tel que pour toute instance I2, elle est en relation R avec I, soit les <I,I2>:R dans Abr*/
                                        setof((I2,C), member((I,I2,R) Abr), L),
                                        /*ajouter les assertions d'instances (I2,C) precedement sauvegardees au noeud en cours de traitement*/
                                        evolue_L(L, Lie,Lpt_suite,Li,Lu,Ls, Lie1,Lpt1,Li1,Lu1,Ls1),
                                        /*affiche_evolution_Abox(Ls, Lie, [(I, all(R,C))|Lpt_suite], Li, Lu, Abr, Ls1,Lie1,Lpt1,Li1,Lu1, Abr ),*/
                                        resolution(Lie1, Lpt1, Li1, Lu1, Ls1, Abr1).


/*afficher C que si il est atomique (condition en principe verifiee car la Abox est sense etre simplifiee et mise sous nnf)*/
affiche_C(C) :- cnamea(C), write(C). 
affiche_C(not(C)) :- write('\u00AC'), affiche_C(C).
affiche_C(and(C1, C2)) :- affiche_C(C1), write('\u2293'), affiche_C(C2).
affiche_C(or(C1, C2)) :- affiche_C(C1), write('\u2294'), affiche_C(C2).
affiche_C(some(R, C)) :- role(R), write('\u2203'), write(R), write('.'), affiche_C(C).
affiche_C(all(R, C)) :- role(R), write('\u2200'), write(R), write('.'), affiche_C(C).


affiche_Abe([]).
affiche_Abe([(I,C)|L]) :- write(I), write(":"), nl, affiche_Abe(L).

affiche_Abr([]).
affiche_Abr([(I,I2, R)|L]) :- write("<"), write(I), write(","),write(I2),write(">"),write(":"),write(R),nl, affiche_Abe(L).



affiche_evolution_Abox(Ls1, Lie1, Lpt1, Li1, Lu1, Abr1, Ls2, Lie2, Lpt2, Li2, Lu2, Abr2) :-
                    write("┌─────────────────────────────────────┐"),
                    write("|            Etat de départ           |"),
                    write("└─────────────────────────────────────┘"),nl,nl,

                    affiche_Abe(Ls1),
                    affiche_Abe(Lie1),
                    affiche_Abe(Lpt1)
                    affiche_Abe(Li1),
                    affiche_Abe(Lu1),
                    affiche_Abr(Abr1),

                    nl,nl,nl,

                    write("┌─────────────────────────────────────┐"),
                    write("|            Etat d'arrivée           |"),
                    write("└─────────────────────────────────────┘"),nl,nl,
                    affiche_Abe(Ls2),
                    affiche_Abe(Lie2),
                    affiche_Abe(Lpt2)
                    affiche_Abe(Li2),
                    affiche_Abe(Lu2),
                    affiche_Abr(Abr2).

                    