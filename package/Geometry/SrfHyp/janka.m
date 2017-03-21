freeze;
// J. Pilnikova.
// Functions to find the lie algebra of the automorphism group of a variety
// defined by the intersection of degree 2 hypersurfaces.
// some updates by JS, March 2008
//
// + additional clause to use LLL when working over Q to get better
//  basis by SRD, March 2013

intrinsic myFindLieAlgebra(I::RngMPol: withId := false) -> Map
{ 
Finds the Lie algebra of the variety defined by the ideal.
The ideal must be given by quadratic generators
}

  //  rank is the number of variables of the ring of I
  rank := Rank(I);
  Q := CoefficientRing(I);

  // need both because reduction is not implemented for matrix spaces
  Qdxd := KMatrixSpace(Q, rank, rank);
  Qd2 := VectorSpace(Q,rank^2);

  // originally bI was computed as MinimalBasis
  // but this poisons the performance. better not use it. JS
  bI := Basis(I);
  if not &and[IsHomogeneous(b) and (TotalDegree(b) eq 2) : b in bI] then
    bI := MinimalBasis(I);
  end if;
  form := [ Qdxd | ];
  vform := [ Qd2 | ];
  for k := 1 to #bI do
    require (IsHomogeneous(bI[k]) and (TotalDegree(bI[k]) eq 2)): 
      "The defining equations are not quadratic forms.";
    form[k] := Qdxd ! SymmetricBilinearForm(bI[k]);
    vform[k] := Qd2 ! Eltseq(form[k]);
  end for;

  // subspace of forms - we need to reduce by it
  VS := sub< Qd2 | vform >;

  //  compute the subspace of Qdxd of all v 
  //  s.t. Transpose(form[i]*v) + form[i]*v is in VS 

  // first equation: trace should be zero if withId is false
  if not withId then
     Bigsys := Transpose(Matrix([ Qd2 | Qd2!Eltseq(ScalarMatrix(rank,1)) ]));
  else
     Bigsys := Matrix(Q,rank^2,0,[]);
  end if;

  // add d^2 equations for each bI
  for i := 1 to #bI do
  
    // condition for i-th Basis element
    Columns := [ Qd2 | ];
    for j := 1 to rank^2 do
      aux := form[i]*Basis(Qdxd)[j];
      Columns[j] := ReduceVector(VS,Qd2!Eltseq(aux + Transpose(aux)));
    end for;
    NewRows := (Matrix(Columns));

    Bigsys := HorizontalJoin(Bigsys,NewRows);
  end for;

  Lrep := Nullspace(Bigsys);

  // Choose a nice basis: saturate, and lll wrt matrix entries
  // March 2013, SRD
  if Type(Q) eq FldRat then
    Qdxd_Z := RMatrixSpace(Integers(), rank, rank);
    Lrep_Z := Saturation(sub< Qdxd_Z | [ClearDenominator(Qdxd!Eltseq(x)) : x in Basis(Lrep)] > );
    Lrep   := RMatrixSpaceWithBasis( ChangeUniverse(LLL(Basis(Lrep_Z)), Qdxd) );
  else
    Lrep   := RMatrixSpaceWithBasis([Qdxd!Eltseq(b) : b in Basis(Lrep)]);
  end if;

  bLrep := Basis(Lrep);

  dim := Dimension(Lrep);

  //  create a structure-constants-Lie-algebra
  T := [];
  for i := 1 to dim do
    for j := 1 to dim do
      cf := Coordinates(Lrep,bLrep[i]*bLrep[j]-bLrep[j]*bLrep[i]);
      for k := 1 to dim do
        if not IsZero( cf[k] ) then
          Append( ~T, <i,j,k, cf[k]> );
        end if;
      end for;
    end for;
  end for;
  if (dim gt 0) and (T eq []) then
    T := [<1,1,1, 0>];
  end if;
  L := LieAlgebra< Q, dim | T >;

  // return the map (L is accessible from it by Domain)
  Rep := hom< L-> Qdxd | [Qdxd!Eltseq(x) : x in bLrep]>;
  return Rep;

end intrinsic;

