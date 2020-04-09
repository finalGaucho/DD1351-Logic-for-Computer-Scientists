% Uppgift 1.
/*
Prolog kommer att binda variabeln X till atom a, variabeln Y
till atom b och sedan binder den även variablen X till Y. 
Men för att binda två variabler kräver de att de är bundna
till samma atom, vilket inte är fallet och därmed
kommer den ge output.
*/


% Uppgift 2.
/*
Vi har två predikat som kollar ifall adam gillar ett visst
ämne, men vi vet att han inte gillar svenska eller historia.
Därför använder vi oss av två stycken predikat där den första
kollar ifall X stämmer för notLike(X), om den gör det använder
vi oss av cut och fail, fail gör att prolog vill använda sig
av backtracking men vår cut gör det ej möjligt, därför får 
vi direkt en output av false. Det är även viktigt att 
vårt negation as failure predikat är först i ordningen, annars
kommer vi alltid få en output av true eftersom den redan hittat en 
korrekt bindning utan att först kolla om den finns i notLike.
*/
subject(matte).
subject(fysik).
subject(historia).
subject(svenska).
subject(engelska).

notLike(svenska).
notLike(historia).

likes(adam, X) :- notLike(X), !, fail.
likes(adam, X) :- subject(X).

% Uppgift 3.
/*
Vårt predikat binder den omvända listan till X vilket gör 
att det sista elementet nu blir vår head. Då väljer vi 
ut den genom select och binder den till E, resten av listan 
binder vi till Y. Därefter använder vi reverse en gång till och 
binder den till R.
*/
findlast([H|T], R, E) :-
    reverse([H|T],[E|T1]),
    reverse(T1, R).


% Uppgift 4.
/*
We need to cover up all possible cases to form all different
combinations of the list for the recursion.
The base-case is the empty list - since there is only
one combination for it. Secondly we want to consider
each head in the list and if we want to include or 
exlude it, this is done with our two recursive predicates.
So when we give a question to prolog it will branch into 
all the multiple outcomes, and for each new iteration
we it can backtrack and choose the other option.
As such for each iteration it can choose to either include
or exclude the head, this also makes it unable to later 
down in the branching choose to reintroduce an excluded
element.
*/
partstring([], []).
partstring([H|T1], [H|T2]) :-
    partstringhelp(T1, T2).
partstring([_|T1], T2) :-
    partstring(T1, T2).

partstringhelp(_,[]).
partstringhelp([H|T1], [H|T2]) :-
    partstringhelp(T1, T2).

% Uppgift 5.
/*
We have the same reasoning here, base-case is the empty list
since there is only one way to permute it. As for any other
list
*/
permute([], []).
permute([H|T], L1) :-
    permute(T, L2),
    select(H, L1, L2).


