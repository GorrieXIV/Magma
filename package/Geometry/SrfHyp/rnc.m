// *********************************************************************
// * Package: rnc.mag                                                  *
// * =============================                                     *
// *                                                                   *
// * Author: Josef Schicho                                             *
// *                                                                   *
// * Email : Josef.Schicho@oeaw.ac.at                                  *
// *                                                                   *
// * Date  : March 2008                                                *
// *                                                                   *
// *                                                                   *
// * Purpose:                                                          *
// * --------                                                          *
// *                                                                   *
// * The Lie algebra method for rational normal curves                 *
// *                                                                   *
// * Dependencies:                                                     *
// * janka.mag                                                         *
// *                                                                   *
// *********************************************************************
freeze;

/* 
   added 01/12 by mch. Gets the "smallest" eigenvalues of the square
   of a Cartan element in the case that the base field is char 0
   but not the rationals so Minimum and Maximum may not work.
*/ 
function get_min_evalue(evs)
// the set of eigenvalues in evs should be of the form
// 1^2*r,2^2*r,..,n^2*r, for some r!=0 and n>=1, each value
// occuring twice. Function returns r

    k := Universe(evs);
    Q := Rationals();
    assert &and[u ne k!0 : u in evs];
    N := #evs;
    if N eq 1 then return evs[1]; end if;
    fracs := [evs[j]/evs[i] : j in [1..N], i in [1..N] | j ne i];
    m := 0; ind := 0;
    for i in [1..#fracs] do
	boo,r := IsCoercible(Q,fracs[i]);
	assert boo;
	if r gt m then m := r; ind := i; end if;
    end for;
    assert m eq (2*N-1)^2;
    return evs[((ind-1) div (N-1))+1];

end function;

// ======================
// = Exported functions =
// ======================


intrinsic ProjKilling(x::AlgLieElt, sa::AlgLie) -> AlgLieElt
{ 
Project an element onto a subalgebra.
This is useful for constructing new representations from old ones.
x must be an element in a semisimple Lie algebra, and sa
must be a subalgebra where the Killing form is nondegenerate.
Otherwise an error is produced by inverting xfer.
}
  L := Parent(x);
  Q := CoefficientRing(L);
  n := Dimension(L);
  m := Dimension(sa);
  KM := KillingMatrix(L);
  V := VectorSpace(Q,n);
  inj := Morphism(sa,L);
  compl := Morphism(Nullspace(KM*Transpose(inj)),V);
  xfer := VerticalJoin(inj,compl);
  E := VerticalJoin(ScalarMatrix(Q,m,1),ZeroMatrix(Q,n-m,m));
  return L!(V!x * xfer^-1 * E * inj);
end intrinsic;

intrinsic FindXYH(L::AlgLie) -> BoolElt, SeqEnum
{
Decides if L is isomophic to sl2.
If yes, computes a basis [x,y,z] such that [x,y]=h, [h,x]=2x, [h,y]=-2y
}

  Q := CoefficientRing(L);
  P2<u,v,w> := ProjectiveSpace(Q,2);
  Nilp := Conic(KillingForm(L));
  isom, pt := HasRationalPoint(Nilp);
  if isom then
    y := L!Coordinates(pt);
    h := L!Eltseq(Solution(Matrix([ L.i*y : i in [1..3]]),-2*y));
    M1 := Matrix( [ h*L.i - 2*L.i : i in [1..3]]);
    M2 := Matrix( [ L.i*y : i in [1..3]]);
    rhs := Vector([Q|0,0,0] cat Eltseq(h));
    x := L!Eltseq(Solution(HorizontalJoin(M1,M2),rhs));
    return true, [L| x,y,h];
  else
    return false, _;
  end if;

end intrinsic;

// parametrize rational normal curve

intrinsic RepChevalleyBasis(Rep) -> BoolElt, SeqEnum
{
find a Chevalley Basis of sl2 by an irreducible representation.
The structure of the codomain must have matrix multiplication
(not Lie bracket multiplication).
}
  L := Domain(Rep);
  Mat := Codomain(Rep);
  Q := CoefficientRing(L);
  if (Dimension(L) ne 3) then
    error "nothing useful available here";
  end if;
  
  C := CartanSubalgebra(L);
  if (Dimension(C) ne 1) then
    error "nothing useful available here";
  end if;
  ar := L!C.1;
  Ar := Rep(ar);
  n := NumberOfRows(Ar); // why cant we detect this from Mat above?

  if IsOdd(n) then // representation is not useful then
    return (FindXYH(L));
  end if;

  if (n eq 2) then // have already 2dim representation
    V4 := VectorSpace(Q,4);
    sys := Matrix([ V4!Eltseq(Rep(L.i)) : i in [1..3] ]);

    solh := Solution(sys,V4![1,0,0,-1]);
    h := &+ [ solh[i] * L.i : i in [1..3] ];
    solx := Solution(sys,V4![0,1, 0,0]);
    x := &+ [ solx[i] * L.i : i in [1..3] ];
    soly := Solution(sys,V4![0,0, 1,0]);
    y := &+ [ soly[i] * L.i : i in [1..3] ];
    return true, [L| x,y,h];
  end if;

  nhalf := Integers()!n/2;

  // get 2dimensional submodule of C
  Aq := Ar * Ar;
  if Q cmpeq Rationals() then
    scal := Minimum([ v[1] : v in Eigenvalues(Aq) ]);
    if ( scal lt 0 ) then 
      scal := Maximum([ v[1] : v in Eigenvalues(Aq) ]);
    end if;
  else
    error if Characteristic(Q) ne 0, 
	"function assumes characteristic 0 base field";
    scal := get_min_evalue([ v[1] : v in Eigenvalues(Aq) ]);
  end if;
  Vn := VectorSpace(Q,n);
  Vs := Eigenspace(Aq,scal);
  if (Dimension(Vs) ne 2) then
    error "module unexpected";
  end if;

  // submatrix extraction for that module decomposition
  Vc := &+ [ Eigenspace(Aq,(2*i+1)^2*scal) : i in [1..nhalf-1]];
  if (Dimension(Vc) ne n-2) then
    error "module unexpected";
  end if;
  T := VerticalJoin(Morphism(Vs,Vn),Morphism(Vc,Vn));
  E := HorizontalJoin(ScalarMatrix(Q,2,1),ZeroMatrix(Q,2,n-2));
  TO := E*T; OT := T^-1*Transpose(E);
  
  // construct a 3D module of L
  Mat2 := MatrixAlgebra(Q,2);
  getblock := map< L -> Mat2 | x :-> TO*Rep(x)*OT >;
  rho := map< L -> Mat2 |
      x :-> 2/n*getblock(x)+(n-2)/n*getblock(ProjKilling(x,C)) >;

  // we know the image of some Chevalley basis
  V4 := VectorSpace(Q,4);
  sys := Matrix([ V4!Eltseq(rho(L.i)) : i in [1..3] ]);

  solh := Solution(sys,V4![1,0,0,-1]);
  h := &+ [ solh[i] * L.i : i in [1..3] ];
  solx := Solution(sys,V4![0,1,0,0]);
  x := &+ [ solx[i] * L.i : i in [1..3] ];
  soly := Solution(sys,V4![0,0,1,0]);
  y := &+ [ soly[i] * L.i : i in [1..3] ];

  return true, [L| x,y,h];
    
end intrinsic;

intrinsic ParametrizeRNC(X::Sch, P1::Sch) -> BoolElt, MapSch, Mtrx
{
find a parametrization of a rational normal curve.
Functionality as ParametrizeRationalNormalCurve in the Schemes package.
}
  I := Ideal(X);
  R := Generic(I);
  n := Rank(R);
  Q := CoefficientRing(I);
  Par<s,t> := CoordinateRing(P1);
  // first trap P1 
  if (n eq 2) then
    para := [s,t];
    parai := [R.1,R.2];
    phi := map<P1 -> X | para,parai>;
    return true, phi, _;
  end if;

  // standard parametrization
  T := [Par | s^(n-i)*t^(i-1) : i in [1..n]];

  Repr := myFindLieAlgebra(I);
  L := Domain(Repr);
  if (Dimension(L) ne 3) then
    error "not a rational normal curve";
  end if;
  isom, CB := RepChevalleyBasis(Repr);
  if not isom then
    return false, _, _;
  end if;

  Xt := Transpose(Repr(CB[1]));
  Yt := Transpose(Repr(CB[2]));
  Ht := Transpose(Repr(CB[3]));
  
  // construct matrix
  Vn := VectorSpace(CoefficientRing(I),n);
  space := Eigenspace(Ht,n-1);
  if (Dimension(space) ne 1) then
    error "module mismatch";
  end if;
  v := Basis(space)[1];
  Vn := VectorSpace(CoefficientRing(I),n);
  Rows := [ Vn | v ];
  for i := 1 to n-1 do
    Rows[i+1] := 1/i * Rows[i] * Yt;
  end for;

  // the result; 
  M := Matrix(Rows);
  Mi := M^-1;
  para := Eltseq(Vector(T) * ChangeRing(M,Par));
  back := Vector([R.i: i in [1..n]]) * ChangeRing(Mi,R);
  parai := [back[1], back[2]];
  // for performance tests, checking should be off
  phi := map<P1 -> X | para,parai: Check:=false, CheckInverse:=false>;
  Major := Matrix(R,2,n-1,[[back[i]:i in [1..n-1]],[back[i]:i in [2..n]]]);

  // check moited because thew MapSch constructor does it
  //ok := &and ([(phi(Basis(I)[i]) eq 0) : i in [1..#Basis(I)] ]);
  //if not ok then
  //  error "final check failed";
  //end if;

  return true,phi,Major;
end intrinsic;

