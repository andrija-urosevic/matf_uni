% 2 plus 2 is 4, minus 1, that's 3 quick maths!

letters(Vs) :- Vs = [T, W, O, F, U, R],
               Vs ins 0..9,
               all_different(Vs),
               2*(100*T + 10*W + O) #= 1000*F + 100*O + 10*U + R,
               label(Vs),
               write(' '), write(T), write(W), write(O), nl,
               write('+'), write(T), write(W), write(O), nl,
               write('----'), nl,
               write(F), write(O), write(U), write(R), nl.
               

