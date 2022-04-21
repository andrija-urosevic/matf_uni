include "globals.mzn";

int: n;

array[1..n,1..n] of int: p;

% Promenljive i domeni
array[1..n,1..n] of var 1..n:x;

% Ogranicenja za redove i kolone
constraint forall(i in 1..n) (alldifferent([x[i,j] | j in 1..n]));
constraint forall(j in 1..n) (alldifferent([x[i,j] | i in 1..n]));

% Ogranicenja iz postavke zadatka
constraint forall(i,j in 1..n) (p[i,j] != 0 -> x[i,j] == p[i,j]);

solve satisfy;