freeze;

SMALLORDER := 2^10;         /* controls work in finger printing */
LARGE := 5 * 10^5;          /* hard work for BirthdayParadox */
SMALL := 5 * 10^2;          /* easy work for BirthdayParadox */
MAXORBITSIZE := 6 * 10^6;   /* largest orbit we will list */
ORBITLIMIT := 1000;         /* max size of a small orbit */
NHITS := 15;                /* number of coincidences */
ORDERLIMIT := 10^5;         /* if subgroup of GL (d, p) remaining has
                               smaller order, don't fingerprint */
DEGREE := 20000;            /* maximum number of spaces to fingerprint */
MAXPARTITION := 64;         /* maximum size of partition to consider
                               for triple intersections */
SMALLORBIT := 100;          /* recurse through p-multiplicator */
MAXSPACES := 400;           /* maximum number of characteristic spaces */
MultiplicatorChop := true;  /* chop up the p-multiplicator */

if assigned MembershipTest eq false then
   MembershipTest := true;  /* willing to test for membership in matrix
                               representation of stabiliser */
end if;

ProbablyTrivial := 3/2;     /* returned as length of orbit when
                               BirthdayParadox believes orbit is trivial */

RF := recformat <perm: GrpPermElt, order: RngIntElt,
                 map: Map, extension: GrpMatElt, type: MonStgElt>;

AutRF := recformat <P: GrpPC, K: GrpPC, PQ : GrpPCpQuotientProc,
                    Capable: BoolElt, Identifier: MonStgElt,
                    complete: BoolElt, Autos: SeqEnum,
                    pAutos: SeqEnum, Order: RngIntElt>;
