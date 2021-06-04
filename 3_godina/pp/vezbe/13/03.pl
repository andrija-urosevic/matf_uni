% Novcici: 1, 2, 5, 10, 20

novcici(Vs) :- Vs = [X1, X2, X5, X10, X20],
               Vs ins 1..50,
               X1 * 1 + X2 * 2 + X5 * 5 + X10 * 10 + X20 * 20 #= 50,
               label(Vs).




