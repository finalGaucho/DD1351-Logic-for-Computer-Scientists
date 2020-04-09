/* Load model, initial state and formula from file. */
verify(Input) :- see(Input), 
read(T), 
read(L), 
read(S), 
read(F), 
seen, 
check(T, L, S, [], F).

/* check(T, L, S, U, F) */

/*
T - The transitions in form of adjacency lists 
L - The labeling 
S - Current state 
U - Currently recorded states 
F - CTL Formula to check. 
*/

/* Should evaluate to true iff the sequent below is valid. 
(T,L), S |- U F */

/* To execute: consult(’your_file.pl’). verify(’input.txt’). */

/*Literals */
check(_, L, S, [], F) :- 
    member([S, List], L),
    member(F, List).

check(_, L, S, [], neg(F)) :- 
    \+ check(_, L, S, [], F).

/* And */ 
check(T, L, S, [], and(F,G)) :- 
    check(T, L, S, [], F),
    check(T, L, S, [], G).

/* Or1 */
check(T, L, S, [], or(F, _)) :- 
    check(T, L, S, [], F).

/* Or2 */
check(T, L, S, [], or(_, G)) :- 
    check(T, L, S, [], G).

/* AX */
check(T, L, S, [], ax(F)) :-
    check(T, L, S, [], neg(ex(neg(F)))).

/* EX */
check(T, L, S, [], ex(F)) :-
    member([S, List], L),
    check(T, List, S, [], F).

/* AG1 */
check(T, L, S, U, ag(F)) :-
    member([S, List], L),
    check(T, List, S, U, F).

/* AG2 */
check(T, L, S, U, ag(F)) :-
    \+ member([S, _], U),
    check(T, L, S, U, F).

/* AF1 */
check(T, L, S, [], af(F)) :-
    check(T, L, S, [], neg(eg(neg(F)))).

/* AF2 */
check(T, L, S, U, af(F)) :-
    \+ member([S, _], U),
    check(T, L, S, U, F).

/* EG1 */
check(T, L, S, U, eg(F)) :-
    member([S, List], L),
    check(T, List, S, U, F).

/* EG2 */
check(T, L, S, [], eg(F)) :-
    \+ member([S, _], L),
    check(T, L, S, [], F).

/* EF1 */
check(T, L, S, [], ef(F)) :-
    check(T, L, S, [], neg(ag(neg(F)))).

/* EF2 */
check(T, L, S, U, ef(F)) :-
    \+ member([S, _], U),
    check(T, L, S, U, F).