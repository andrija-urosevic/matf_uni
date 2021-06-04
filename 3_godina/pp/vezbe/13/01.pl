% Primer programiranja ogranicenje

primer(Vs) :- Vs = [X, Y, Z],
              X in 1..3,
              Y in 2..10,
              Z in 5..8,
              Z #>= Y,
              label(Vs).

% Potpun kvadrat
potpun(Vs) :- Vs = [X],
              X in 1..100,
              Y * Y #= X,
              label(Vs).

