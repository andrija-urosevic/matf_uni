include "globals.mzn";

var 1..72: P;
var 1..72: G;
var 1..72: K;

constraint 59 - 13 <= P + G + K;
constraint P + G + K <= 29 + 13;

constraint 15 - 13 <= P + G;
constraint P + G <= 15 + 13;

constraint 18 - 13 <= G + K;
constraint G + K <= 18 + 13;

constraint 20 - 13 <= K + P;
constraint K + P <= 20 + 13;

solve satisfy;
