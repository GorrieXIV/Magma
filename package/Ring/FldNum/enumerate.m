freeze;

// SRD, October 2013

/* Examples

F<w> := NumberField(x^4 - NextPrime(10^5));
F<w> := NumberField(x^4 - x^3 + 5*x^2 - 7*x + 12);

SE := ShortElements(Integers(F), 1000);
[Norm(x) : x in SE];
[RealField(4)| AbsoluteLogarithmicHeight(x) : x in SE];

*/

// Undocumented currently

intrinsic ShortElements(O::RngOrd, B::RngElt 
                       : Precision:=GetKantPrecision()) 
       -> SetIndx

{The set of elements which have length at most B as vectors 
in the Minkowski lattice (up to some round-off errors)}

  // require B integer or real

  LLLO := LLL(O);
  L := MinkowskiLattice(LLLO);
  G := GramMatrix(L);
//ChangeRing(G, RealField(6));

  s := 10 ^ Precision;
  GZ := Matrix(Integers(), Ncols(G), 
              [Round(s*g) : g in Eltseq(G)]);
  LZ := LatticeWithGram(GZ);

  SV := ShortVectors(LZ, Ceiling(s*B^2));
  elts := [O| LLLO! Coordinates(t[1]) : t in SV];
  return elts;
end intrinsic;

