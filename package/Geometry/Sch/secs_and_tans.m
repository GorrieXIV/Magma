freeze;

/////////////////////////////////////////////////////////////////
//  Functions related to the secant and tangent varieties of   //
//         affine and ordinary projective schemes.             //
//           Mike Harrison 05/2004                             //
/////////////////////////////////////////////////////////////////

/**** Functions for the secant variety *************************/

// computes the secant variety of an affine scheme.
function SecantsAffine(X)

  Aff := AmbientSpace(X);
  Paff := CoordinateRing(Aff);
  n := Rank(Paff);
  Pa2 := PolynomialRing(BaseRing(Paff),2*n+1);
  inc1 := hom<Paff -> Pa2 | [Pa2.j : j in [2..n+1]]>;
  inc2 := hom<Paff -> Pa2 | [Pa2.j : j in [n+2..2*n+1]]>;
  prj2 := hom<Pa2 -> Paff | [0: j in [1..n+1]] cat
                                 [Paff.j : j in [1..n]]>;
  newvars := hom<Pa2 -> Pa2 | [Pa2.1] cat
              [Pa2.(n+j) - Pa2.1 * Pa2.j : j in [2..n+1]] cat
              [Pa2.(n+j) + (1-Pa2.1) * Pa2.j : j in [2..n+1]] >;

  /* newvars change of variables from
    (t,x1,..,xn,y1,..yn) to (t,u1,..,un,v1,..vn)
    with ui = yi-xi       vi = xi+t*(yi-xi)  
         xi = vi-t*ui     yi = vi+(1-t)*ui          */

  // get ideal of Line x Xaff x Xaff in Spec(Pa2) and
  // make variable change so that the secant map becomes
  // a projection on the last n variable space
  Ia2 := ideal<Pa2 | [newvars(inc1(b)): b in B],
           [newvars(inc2(b)): b in B]> where B is Basis(Ideal(X));
   
  Isecs := EliminationIdeal(Ia2,n+1); // do the projection!
  Isecs := ideal<Paff | [prj2(b) : b in Basis(Isecs)]>; 
  return Scheme(Aff,Isecs);
  
end function;

// Main function for the computation of the secant variety
// of an affine or projective scheme.
// NB. Assumed in the projective case that there is a
//  standard affine patch intersecting every component of X.
intrinsic SecantVariety(X::Sch : PatchIndex := 0) -> Sch
{ Returns the secant variety of X. }

  require (IsOrdinaryProjective(X) or IsAffine(X)) :
         "Scheme should be affine or ordinary projective.";
  if IsAffine(X) then
     return SecantsAffine(X);
  end if;
  Proj := AmbientSpace(X);
  n := Dimension(Proj);
  require (PatchIndex ge 0) and (PatchIndex le n+1) :
     "That was an illegal patch index";
  if PatchIndex eq 0 then
    I := Ideal(X);
    col_ids := [Parent(I)|];
    for j in [1..2] do
      for i := n+1 to 1 by -1 do
        col := ColonIdeal(I,Proj.i);
        if col subset I then // Proj.i != 0 patch will do
           ind := i; break j; 
	end if;
        if j eq 1 then Append(~col_ids,col); end if;
      end for;
      error if j eq 2, "Couldn't find a good standard affine patch.";
      I := &meet col_ids; // replace I by it's saturation w.r.t.
                          // the redundant ideal.
    end for;
  else
    ind := n+2-PatchIndex;
  end if;

  return ProjectiveClosure(
              SecantsAffine(AffinePatch(X,n+2-ind)));

end intrinsic;

intrinsic IsInSecantVariety(X::Sch,P::Pt) -> BoolElt
{ Returns whether P is in the secant variety of X or not. }

  require IsOrdinaryProjective(X) :
         "Scheme should be ordinary projective";
  Proj := AmbientSpace(X);
  require P in Proj: "Point not in the ambient space.";
  coords := Coordinates(P);
  PR := CoordinateRing(Proj);
  Fs := Basis(Ideal(X));
  n := Rank(PR);
  Q := PolynomialRing(BaseRing(PR),n+1);
  I_test := ideal<Q | [Evaluate(F,[Q.i : i in [2..n+1]]) : F in Fs] cat
                 [Evaluate(F,[coords[i] - (Q.1)*(Q.(i+1)) : i in [1..n]]) :
                                F in Fs] >;
  return IsProper(I_test);
  
end intrinsic;

/********* Functions for the tangent variety ****************/

// computes the tangent variety of an affine scheme.
function TangentsAffine(X)

  Aff := AmbientSpace(X);
  Paff := CoordinateRing(Aff);
  n := Rank(Paff);
  K := BaseRing(Aff);
  P2n := PolynomialRing(K,2*n);

  inc1 := hom<Paff -> P2n | [P2n.j : j in [1..n]]>;
  prj2 := hom<P2n -> Paff | [0:j in [1..n]] cat [Paff.j : j in [1..n]]>;
  
  JMat := JacobianMatrix(X);

  I :=  ideal<P2n| [inc1(b) : b in Basis(Ideal(X))]> +
        ideal<P2n| [ &+[(P2n.(j+n)-P2n.j)*inc1(JMat[k,j]) : j in [1..n]] :
                                   k in [1..NumberOfRows(JMat)]]> ;
  I := EliminationIdeal(I,n);
  return Scheme(Aff,ideal<Paff|[prj2(b):b in Basis(I)]>);
 
end function;

// computes the tangent variety of an projective scheme directly
// - ie, without working on an affine patch.
function TangentsProj(X)

  Proj := AmbientSpace(X);
  PR := CoordinateRing(Proj);
  n := Rank(PR);
  JMat := JacobianMatrix(X);
  Proj2,prjs := DirectProduct(Proj,Proj);
  PR2 := CoordinateRing(Proj2);//PolynomialRing(BaseRing(PR),2*n);
  h := hom<PR -> PR2 | [PR2.i : i in [1..n]]>;
  h1 := hom<PR2 -> PR | [0 : i in [1..n]] cat [PR.i : i in [1..n]]>;
  I := ideal<PR2| [h(b) : b in Basis(Ideal(X))]> +
        ideal<PR2| [ &+[PR2.(n+j)*h(JMat[i,j]) : j in [1..n]] :
                                   i in [1..NumberOfRows(JMat)]]>;
  I1 := &meet [ColonIdeal(I,PR2.i): i in [1..n]];
         //saturation wrt max ideal of first product component
  I1 := EliminationIdeal(I1,n);
  I1 := ideal<PR | [h1(b) : b in Basis(I1)]>;
  return Scheme(Proj,I1);
  
end function;

// Main function for the computation of the tangent variety
// of an affine or projective scheme.
intrinsic TangentVariety(X::Sch: PatchIndex := 0) -> Sch
{ Returns the tangent variety of X. }

  require (IsOrdinaryProjective(X) or IsAffine(X)) :
         "Scheme should be affine or ordinary projective.";
  if IsAffine(X) then
     return TangentsAffine(X);  
  end if;
  if PatchIndex eq 0 then
     return TangentsProj(X);
  end if;

  Proj := AmbientSpace(X);
  n := Dimension(Proj);
  require (PatchIndex gt 0) and (PatchIndex le n+1) :
     "That was an illegal patch index";

  return ProjectiveClosure(
               TangentsAffine(AffinePatch(X,PatchIndex)));

end intrinsic;

intrinsic IsInTangentVariety(X::Sch,P::Pt) -> BoolElt
{ Returns whether P is in the tangent variety of X or not. }

  require IsOrdinaryProjective(X):
              "Scheme should be ordinary projective";
  Proj := AmbientSpace(X);
  require P in Proj: "Point not in the ambient space.";
  coords := Coordinates(P);
  PR := CoordinateRing(Proj);
  n := Rank(PR);
  JMat := JacobianMatrix(X);
  I_X := Ideal(X);
  I_test := I_X + ideal<PR | [&+[coords[j]*JMat[i,j] : j in [1..n]] :
                                  i in [1..NumberOfRows(JMat)]]>;
  return (Dimension(I_test) gt 0);
  
end intrinsic;
