% ABCDE, td. A + 2B - 3C + 4D - 5E minimalno, A, B, C, D, E razlicite
petocifren :- Vs = [A, B, C, D, E],
              Vs ins 0..9,
              A #\= 0,
              all_different(Vs),
              labeling([min(A + 2 * B - 3 * C + 4 * D - 5 * E)], Vs),
              Num is 1000*A + 100*B + 10*C + E,
              write(Num), nl.

