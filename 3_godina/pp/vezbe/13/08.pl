% 1   3
%  2 4
%   5
%  6 8
% 7   9

xsic(Vs) :- Vs = [X1, X2, X3, X4, XY, Y1, Y2, Y3, Y4],
            Vs ins 1..9,
            all_different(Vs),
            X1 + X2 + X3 + X4 + XY #= 25,
            Y1 + Y2 + Y3 + Y4 + XY #= 25,
            X1 #< X2, X2 #< XY, XY #< X3, X3 #< X4,
            Y1 #< Y2, Y2 #< XY, XY #< Y3, Y3 #< Y4,
            label(Vs),
            write(X1), write('   '), write(Y1), nl,
            write(' '), write(X2), write(' '), write(Y2), nl,
            write('  '), write(XY), nl,
            write(' '), write(X3), write(' '), write(Y3), nl,
            write(X4), write('   '), write(Y4), nl.


