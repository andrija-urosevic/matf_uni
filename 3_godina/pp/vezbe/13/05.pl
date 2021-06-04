% X >= Z, X * 2 + Y * X + Z<= 34, X in {1,2,...,90}, Y in {2,4,6,...,60}, Z in {1, 10, 20,...,100}
uslov(Vs) :- Vs = [X, Y, Z],
             X in 1..90,
             Y in 2..60,
             Z in 1..100,
             mod(Y, 2) #= 0,
             (Z #= 1; mod(Z, 10) #= 0),
             X #>= Z,
             X * 2 + Y * X + Z #=< 34,
             label(Vs).
