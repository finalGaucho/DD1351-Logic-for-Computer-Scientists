verify(InputFileName) :-
	see(InputFileName),
	read(Prems), 
    read(Goal), 
    read(Proof),
	seen,
	valid_proof(Prems, Goal, Proof).

/*
Algoritm för genomgång av beviset. 
*/

valid_proof(Prems, Goal, Proof) :- 
    valid_rows([], Prems, Goal, Proof).

/* Sista elementet i en lista är alltid den tomma, om föregående är Goal har hela listan gåtts igenom och är godkänd */
valid_rows([[_, Goal, _]|_], _, Goal, []). 

/* Om det finns en box inom en rad, kör valid_box på den raden och forsätt på nästa rad utanför boxen i valid_row */
valid_rows(Already_Valid, Prems, Goal, [[[BoxRow, BoxResult, assumption]|RestOfTheBox]|RestOfRows]) :-
    valid_box([[BoxRow, BoxResult, assumption]|Already_Valid], Prems, Goal, RestOfTheBox),
    valid_rows([[[BoxRow, BoxResult, assumption]|RestOfTheBox]|Already_Valid], Prems, Goal, RestOfRows).

/* Den går igenom listan rad för rad och kollar med redan godkända rader genom valid_rule */
valid_rows(Already_Valid, Prems, Goal, [OneRow|RestOfRows]) :-
    valid_rule(Already_Valid, Prems, OneRow),
    valid_rows([OneRow|Already_Valid], Prems, Goal, RestOfRows).

/* Följer samma metodik, om sista delen i listan är den tomma listan är vi klara med boxen */
valid_box(_ , _, _, []).

/* Den går igenom boxen rad för rad (exkluderat antagandet i början) och skickar varje rad 
för verifiering i rules */
valid_box(Already_Valid_InBox, Prems, Goal, [BoxRow|RestOfBox]) :-
    valid_rule(Already_Valid_InBox, Prems, BoxRow),
    valid_box([BoxRow|Already_Valid_InBox], Prems, Goal, RestOfBox).

valid_box(Already_Valid, Prems, Goal, [[[SubBoxRow, SubBoxResult, assumption]|RestOfSubBox]|RestOfBox]) :-
    valid_sub_box([[SubBoxRow, SubBoxResult, assumption]|Already_Valid], Prems, Goal, RestOfSubBox),
    valid_box([[[SubBoxRow, SubBoxResult, assumption]|RestOfSubBox]|Already_Valid], Prems, Goal, RestOfBox).

valid_sub_box(_, _, _, []).

valid_sub_box(Already_Valid_InBox, Prems, Goal, [SubBoxRow|RestOfSubBox]) :-
    valid_rule(Already_Valid_InBox, Prems, SubBoxRow),
    valid_box([SubBoxRow|Already_Valid_InBox], Prems, Goal, RestOfSubBox).




/*
Regler för naturlig deduktion.
*/
valid_rule(_Validated, Prems, [_Row, Result, premise]) :-
    member(Result, Prems).

/* Negation elimination */
valid_rule(Validated ,_Prems, [_Row, Result, negnegel(Row2)]) :-
    member([Row2, neg(neg(Result)), _], Validated).

/* Negation introduktion */
valid_rule(Validated, _Prems, [_Row, neg(neg(Result)), negnegint(Row2)]) :-
    member([Row2, Result, _], Validated).

/* Implikation elimination */
valid_rule(Validated, _Prems, [_Row, Result, impel(BasicRow, ImpRow)]) :-
    member([ImpRow, imp(X, Result), _], Validated),
    member([BasicRow, X, _], Validated).

/* Och introduktion */ 
valid_rule(Validated, _Prems, [_Row, and(Y,X), andint(FirstAtom, SecondAtom)]) :-
    member([FirstAtom, Y, _], Validated),
    member([SecondAtom, X, _], Validated).

/* Och_1 elimination */
valid_rule(Validated, _Prems, [_Row, Result, andel1(Row)]) :-
    member([Row, and(Result, _), _], Validated).

/* Och_2 elimination */
valid_rule(Validated, _Prems, [_Row, Result, andel2(Row)]) :-
    member([Row, and(_, Result), _], Validated).

/* Eller_1 introduktion */
valid_rule(Validated, _Prems, [_Row, or(Result, _), orint1(Row)]) :-
    member([Row, Result, _], Validated).

/* Eller_2 introduktion */
valid_rule(Validated, _Prems, [_Row, or(_, Result), orint2(Row)]) :-
    member([Row, Result, _], Validated).

/* MT */
valid_rule(Validated, _Prems, [_Row, neg(Result), mt(NegRow, ImpRow)]) :-
    member([NegRow, imp(Result, X), _], Validated),
    member([ImpRow, neg(X), _], Validated).

/* Implikation introduktion */
valid_rule(Validated, _Prems, [_Row, imp(X,Y), impint(AssumptionRow, SecondRow)]) :-
    look_for_row_in_box(AssumptionRow, Validated, TheGoodBox),
    member([AssumptionRow, X, assumption], TheGoodBox),
    member([SecondRow, Y, _], TheGoodBox).

/* Copy */
valid_rule(Validated, _Prems, [_Row, Result, copy(Row)]) :-
    member([Row, Result, _], Validated).

/* Negation introduktion */
valid_rule(Validated, _Prems, [_Row, neg(Result), negint(AssumptionRow, ContradictionRow)]) :-
    look_for_row_in_box(AssumptionRow, Validated, TheGoodBox),
    member([AssumptionRow, Result, assumption], TheGoodBox),
    member([ContradictionRow, cont, _], TheGoodBox).

/* PBC */
valid_rule(Validated, _Prems, [_Row, Result, pbc(AssumptionRow, ContradictionRow)]) :-
    look_for_row_in_box(AssumptionRow, Validated, TheGoodBox),
    member([AssumptionRow, neg(Result), assumption], TheGoodBox),
    member([ContradictionRow, cont, _], TheGoodBox).

/* Negation contradiction */
valid_rule(Validated, _Prems, [_Row, cont, negel(FirstRow,SecondRow)]) :-
    member([FirstRow, Result, _], Validated),
    member([SecondRow, neg(Result), _], Validated).

valid_rule(Validated, _Prems, [_Row, cont, negel(FirstRow,SecondRow)]) :-
    member([FirstRow, neg(Result), _], Validated),
    member([SecondRow, Result, _], Validated).

/* Eller elimination */
valid_rule(Validated, _Prems, [_Row, X, orel(OrRow, RowAs1, RowX1, RowAs2, RowX2)]) :-
    look_for_row_in_box(RowAs1, Validated, TheGoodBox1),
    look_for_row_in_box(RowAs2, Validated, TheGoodBox2),
    member([OrRow, or(V,Y), _], Validated),
    member([RowAs1, V, assumption], TheGoodBox1),
    member([RowAs2, Y, assumption], TheGoodBox2),
    member([RowX1, X, _], TheGoodBox1),
    member([RowX2, X, _], TheGoodBox2).

/* cont elimination */
valid_rule(Validated, _Prems, [_Row, _, contel(ContradictionRow)]) :-
    member([ContradictionRow, cont, _], Validated).

/* LEM */
valid_rule(_Validated, _Prems, [_Row, or(X,neg(X)), lem]).

/* Since our Already_Valid is a list, our confirmed box will 
be a list inside each list, as such we need to go into each
list and check for elements there! */
look_for_row_in_box(TheGoodRow, [TheGoodBox|_], TheGoodBox) :-
    member([TheGoodRow, _, _], TheGoodBox).

/* If the row we are looking for is not the first one
keep looking.. */
look_for_row_in_box(TheGoodRow, [_|Validated], TheGoodBox) :-
    look_for_row_in_box(TheGoodRow, Validated, TheGoodBox).

