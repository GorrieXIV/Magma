////////////////////////////////////////////////////////////////////////
//                                                                    //
//                  LATTICES OF BINARY QUADRATIC FORMS                //
//                            David Kohel                             //
//                      Last modified April 2001                      //
//                                                                    //
////////////////////////////////////////////////////////////////////////

freeze;

// Intrinsics: Lattice, ThetaSeries, RepresentationNumber

intrinsic Lattice(f::QuadBinElt) -> Lat
   {The Lattice of the binary quadratic form f.}
   D := Discriminant(f);
   require D lt 0 : "Discriminant of form must be negative";
   return LatticeWithGram(Matrix(2,2,[ f[1], f[2]/2, f[2]/2, f[3] ]));
end intrinsic;

intrinsic RepresentationNumber(f::QuadBinElt,n::RngIntElt) -> RngIntElt
   {The nth representation number of the form f.}
   require Discriminant(f) lt 0 : "Discriminant of form must be negative";
   L := LatticeWithGram(Matrix(2,2,[ 2*f[1], f[2], f[2], 2*f[3] ]));
   return Integers()!Coefficient(ThetaSeries(L,2*n+1),2*n);
end intrinsic;

intrinsic ThetaSeries(f::QuadBinElt,n::RngIntElt) -> RngSerElt
   {The theta series of the binary quadratic form f.}
   require Discriminant(f) lt 0 : "Discriminant of form must be negative";
   L := LatticeWithGram(Matrix(2,2,[ 2*f[1], f[2], f[2], 2*f[3] ]));
   t := ThetaSeries(L,2*n+1);
   S := Parent(t);
   return S![ Coefficient(t,2*k) : k in [0..n] ] + O(S.1^(n+1));
end intrinsic;

