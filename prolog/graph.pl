edge(a,e).
edge(e,d).
edge(d,c).
edge(c,b).
edge(b,a).
edge(d,a).
edge(e,c).
edge(f,b).
path(A,B,Path) :- travel(A,B,[A],Q).
travel(A,B,P,[B|P]) :- edge(A,B).
travel(A,B,Visited,Path) :- 
	edge(A,C), 
	C \== B, 
	\+member(C,Visited),
	travel(C,B,[C|Visited],Path).
cycle(X):- path(X,Y,TempPathOne), X \== Y, path(Y,X,TempPathTwo).

/* Example:
?- cycle(e).
true .
?- cycle(f).
false.
*/
