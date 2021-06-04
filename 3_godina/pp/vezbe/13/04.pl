% magicni kvadrat

magic :- Vs = [X11, X12, X13, X21, X22, X23, X31, X32, X33],
         Vs ins 1..9,
         all_different(Vs),
         X11 + X12 + X13 #= 15,
         X21 + X22 + X23 #= 15,
         X31 + X32 + X33 #= 15,
         X11 + X21 + X31 #= 15,
         X12 + X22 + X32 #= 15,
         X13 + X23 + X33 #= 15,
         X11 + X22 + X33 #= 15,
         X13 + X22 + X31 #= 15,
         label(Vs),
         write(X11), write(" "), write(X12), write(" "), write(X13), nl,
         write(X21), write(" "), write(X22), write(" "), write(X23), nl,
         write(X31), write(" "), write(X32), write(" "), write(X33), nl.


