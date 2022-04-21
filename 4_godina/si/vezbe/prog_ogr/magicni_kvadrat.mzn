include "globals.mzn";

% Definisemo promenljive i domen
array[1..4,1..4] of var 1..16: x;

% Ogranicenja iz zadatka
constraint x[1,2] == 12;
constraint x[2,2] == 8;
constraint x[2,3] == 15;
constraint x[3,1] == 7;
constraint x[3,3] == 2;
constraint x[4,1] == 4;
constraint x[4,4] == 11;

% Suma svih redova i kolona mora biti 34
constraint forall([sum([x[i,j] | j in 1..4]) == 34 | i in 1..4]);
constraint forall([sum([x[i,j] | i in 1..4]) == 34 | j in 1..4]);

% Suma svih dijagonala mora biti 34
constraint sum([x[i,i] | i in 1..4]) == 34;
constraint sum([x[i,5-i] | i in 1..4]) == 34;

% Svako polje mora imati drugaciju vrednost
constraint alldifferent([x[i,j] | i, j in 1..4]);

solve satisfy;
