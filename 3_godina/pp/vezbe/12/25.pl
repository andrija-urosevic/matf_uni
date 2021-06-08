% nzd(N, M, NZD) <- NZD == NZD(N, M)?
% nzs(N, M, NZS) <- NZS == NZS(N, M)?

nzd(N, 0, N) :- !.
nzd(N, M, NZD) :- P is N mod M, nzd(M, P, NZD).

nzs(N, M, NZS) :- nzd(N, M, P), NZS is (N*M) // P.

