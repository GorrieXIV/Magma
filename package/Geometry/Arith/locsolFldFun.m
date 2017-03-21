freeze;

// A version of the generic IsLocallySolvable function for schemes over function fields.
// This should work for general nonsingular affine or projective schemes. 
// I've also put in some extra code to make it work in the weighted projective case.
// (this extra stuff could also be copied back into the number field case if we want to 
//  make the generic routine work in the weighted projective case -- note though that
//  hyperelliptics are handled by a special case there).
//
// Steve

import "loctools.m": MinValuation, ShiftVal, CoefficientByExponentVector, StripPrecisionlessTerms;

///////////////////////////////////////////////////////
// Smooth local solubility tester

// Hacked by Steve

function HasIntegralPoints(L,d,resmap)
  //takes a list of polynomials L and an assumed dimension d and looks for
  //integral points. (assumes no rational singular points exist!)
  //returns false,_ or true,[coordinates].

  // resmap is the residue map from the coefficient ring (a local field)
  // to the residue field.

  //some quantities that don't change during the computations.
  Rpol:=Universe(L);
  L:=[MyPrimitivePart(Q) : P in L | Q ne 0 where Q:=StripPrecisionlessTerms(P)];
  R:=BaseRing(Rpol);
  error if not ISA(Type(R),RngSer), "must have polynomials over local ring";
  u:=UniformizingElement(R);
  n:=Rank(Rpol);
  cd:=n-d;
  /*
  if cd ne #L and d eq 0 then
    vprint LocSol,1: "0 dimensional non-complete intersection. Using cluster code";
    V:=AllIntegralPoints(L,Minim([MinPrec(l):l in L]));
    if #V eq 0 then
      return false,_;
    else
      return true, Rep(V);
    end if;
  end if;
  */
  error if not #L eq cd, "Can only handle complete intersections if of positive dimension.";
  k<aa> := Codomain(resmap);
  Rtok := resmap;
  Ak:=AffineSpace(k,n);
  kpol:=CoordinateRing(Ak);
  Rpoltokpol_mons:=hom<Rpol->kpol|[kpol.i:i in [1..n]]>;
  Rpoltokpol := map< Rpol -> kpol | 
                      rr :-> &+[ Rtok(coeffs[i]) * Rpoltokpol_mons(mons[i]) : i in [1..#mons]]
                     where coeffs:=Coefficients(rr) where mons:=Monomials(rr) >;
  // IMPORTANT NOTE: evaluating Rpoltokpol takes time, if the size of the residue field is not tiny!

  //the hard (recursive) work.
  test:=function(L,lvl : try_all_kpoints:=false)
    vprint LocSol,1: "Entering test level ",lvl;
    vprint LocSol,2: "Passed argument:",L;
    L:=[MyPrimitivePart(Q) : P in L | Q ne 0 where Q:=StripPrecisionlessTerms(P)];
    vprint LocSol,2: "Primmed and stripped:",L;
    error if #L lt cd, "Variety appears to have too high dimension. Precision loss?";

    // Check valuations of coefficients to see if reduction is a constant (if so, return false)
    for eqn in L do 
      coeff_vals := [Valuation(c) : c in Coefficients(eqn)];
      mons := Monomials(eqn);
      if &and[ coeff_vals[i] gt 0 xor TotalDegree(mons[i]) eq 0 : i in [1..#mons]] then
        // the reduction of eqn is a nonzero constant poly in kpol, hence no integral sols
        vprint LocSol,2: "Reduction is nonzero constant. Leaving test level ",lvl;
        return false,_;
      end if;
    end for;

    Lk:=[Rpoltokpol(P):P in L];  // the reduction of L

    // New part 
    // If some variables don't appear in the reduction at all,
    // there's no need to consider every value of those variables
    // when listing the points on the reduction; one representative
    // for each will do. 
    // In that case we use this modified version of the usual code.

    missing_vars := [ i : i in [1..Rank(kpol)] 
                    | &and[ lk eq Evaluate(lk,[j eq i select 0 else kpol.j : j in [1..Rank(kpol)]]) 
                          : lk in Lk ] ];     
    assert #missing_vars lt Rank(kpol);
  
    if #missing_vars gt 0 then
      // Get rational points just in terms of the other variables
      Lkschm_slice := Scheme(Ak, Lk cat [kpol.i : i in missing_vars]);
      try_all_kpoints or:= #k^Dimension(Lkschm_slice) le 10^4;
      kpoints_on_slice := try_all_kpoints select RationalPoints(Lkschm_slice)  
                                           else [Random(Lkschm_slice(k)) : i in [1..100]];
      vprint LocSol,2: "Points on reduction (representative set):", kpoints_on_slice;

      // Skip this if the entire reduction is singular 
      assert #L eq 1;
      partial_derivs := [Derivative(Lk[1],i) : i in [1..Rank(Rpol)]];
      if not &and[ pd eq 0 : pd in partial_derivs] then
        vprint LocSol,2: "Testing if there are any smooth ones ...";
        J:=JacobianMatrix(Lk);
        for p in kpoints_on_slice do
          Jp := Matrix(Ncols(J), [ Evaluate(f,Eltseq(p)) : f in Eltseq(J) ]);
          E,T:=EchelonForm(Jp);
          rk:=Rank(E);
          error if rk gt cd, "Jacobian has too large a rank. d wrong?";
          if rk eq cd then
            vprint LocSol,2: "Found ",p,". This point will lift."; 
            vprint LocSol,2: "Leaving test level ",lvl;
            return true,[c@@Rtok+O(u):c in Eltseq(p)];
          end if;
        end for;
      end if;

      vprint LocSol,1: "No smooth points. Looking around each point ...";
      for p in kpoints_on_slice do
        vprint LocSol,2: "Looking around ",p,"...";
        // don't lift at the 'missing variables':
        uu := [ (i in missing_vars) select 1 else u : i in [1..Rank(Rpol)] ];
        plift:=[Rpol!(p[i]@@Rtok) + uu[i]*Rpol.i : i in [1..n]];
        L2:=[MyPrimitivePart(Evaluate(f,plift)):f in L];
        repeat
          B:=Matrix([[Rtok(CoefficientByExponentVector(f,
                             [j eq i select 1 else 0:j in [1..n]])):
                                 i in [1..Rank(Rpol)]]:f in L2]);
          E,T:=EchelonForm(B);
          vprint LocSol,2:"Changing the basis of the ideal by:",T;
          TT:=Matrix(Rpol,Ncols(T),Nrows(T),[a@@Rtok:a in Eltseq(T)]);
          L2:=Eltseq(Vector(L2)*Transpose(TT));
          flag:=false;
          vprint LocSol,2:"to",L2;
          for i in [1..#L2] do
            v:=MinValuation(L2[i]);
            if v gt 0 then
              L2[i]:=ShiftVal(L2[i],-v);
              vprint LocSol,2:"Extra content",v,"removed from",i,"th polynomial";
              flag:=true;
            end if;
          end for;
        until not(flag); 
        vprint LocSol,2:"Newly obtained basis is:",L2;
        
        IndentPush();
        rs,pt:=$$(L2,lvl+1);
        IndentPop();
        if rs then
          vprint LocSol,2: "Found a point. We tranform it back and return.";
          vprint LocSol,2: "Leaving test level ",lvl;
          return true,[Evaluate(c,pt):c in plift];
        end if;
      end for;
    
    else // #missing_vars eq 0
      Lkschm:=Scheme(Ak,Lk);
      try_all_kpoints or:= #k^Dimension(Lkschm) le 10^4;
      kpoints:= try_all_kpoints select RationalPoints(Lkschm)  
                                 else [Random(Lkschm(k)) : i in [1..100]];
      indices:=[1..#kpoints];
      vprint LocSol,2: "Points on reduction:",kpoints;

      // Skip this if the entire reduction is singular 
      assert #L eq 1;
      partial_derivs := [Derivative(Lk[1],i) : i in [1..Rank(Rpol)]];
      if not &and[ pd eq 0 : pd in partial_derivs] then
        vprint LocSol,2: "Testing if there are any smooth ones ...";
        J:=JacobianMatrix(Lk);
        while #indices gt 0 do 
          idx := Random(indices);  p := kpoints[idx];  Exclude(~indices,idx);
          if #L eq 1 and &and[ Evaluate(pd,Eltseq(p)) eq 0 : pd in partial_derivs] then 
            continue; end if;
          Jp := Matrix(Ncols(J), [ Evaluate(f,Eltseq(p)) : f in Eltseq(J) ]);
          E,T:=EchelonForm(Jp);
          rk:=Rank(E);
          error if rk gt cd, "Jacobian has too large a rank. d wrong?";
          if rk eq cd then
            vprint LocSol,2: "Found ",p,". This point will lift."; 
            vprint LocSol,2: "Leaving test level ",lvl;
            return true,[c@@Rtok+O(u):c in Eltseq(p)];
          end if;
        end while;
      end if;

      vprint LocSol,1: "No smooth points. Looking around each point ...";
      for p in kpoints do
        vprint LocSol,2: "Looking around ",p,"...";
        plift:=[Rpol!(p[i]@@Rtok) + u*Rpol.i : i in [1..n]];
        L2:=[MyPrimitivePart(Evaluate(f,plift)):f in L];
        repeat
          B:=Matrix([[Rtok(CoefficientByExponentVector(f,
                             [j eq i select 1 else 0:j in [1..n]])):
                                 i in [1..Rank(Rpol)]]:f in L2]);
          E,T:=EchelonForm(B);
          vprint LocSol,2:"Changing the basis of the ideal by:",T;
          TT:=Matrix(Rpol,Ncols(T),Nrows(T),[a@@Rtok:a in Eltseq(T)]);
          L2:=Eltseq(Vector(L2)*Transpose(TT));
          flag:=false;
          vprint LocSol,2:"to",L2;
          for i in [1..#L2] do
            v:=MinValuation(L2[i]);
            if v gt 0 then
              L2[i]:=ShiftVal(L2[i],-v);
              vprint LocSol,2:"Extra content",v,"removed from",i,"th polynomial";
              flag:=true;
            end if;
          end for;
        until not(flag); 
        vprint LocSol,2:"Newly obtained basis is:",L2;
        
        IndentPush();
        rs,pt:=$$(L2,lvl+1);
        IndentPop();
        if rs then
          vprint LocSol,2: "Found a point. We tranform it back and return.";
          vprint LocSol,2: "Leaving test level ",lvl;
          return true,[Evaluate(c,pt):c in plift];
        end if;
      end for;
    end if; // #missing_vars gt 0
    if not try_all_kpoints then 
      return $$(L,0 : try_all_kpoints); end if;
    vprint LocSol,2: "Leaving test level ",lvl;
    return false,_;
  end function;
  
  rs,pt:=test(L,1);
  if rs then
    return true,pt;
  else
    return false,_;
  end if;
end function;


//////////////////////////////////////////////////////
// general local solubility tester. Recurses into the singular locus.

forward IsLocallySolvable1;

intrinsic IsLocallySolvable(X::Sch, pl::PlcFunElt : completion_map:=0) -> BoolElt, Pt
{Tests local solubility of the scheme X (defined over a function field) at the specified place}

  require IsAffine(X) or IsProjective(X) : "Variety must be affine or projective";
  require Dimension(X) ge 1 and Dimension(Ambient(X)) ge 2 : 
         "Zero-dimensional schemes are not allowed, neither are ambient spaces";
  require IsIrreducible(X) and IsNonsingular(X) : 
         "Scheme should be irreducible and nonsingular";
  return IsLocallySolvable1(X, pl : completion_map:=completion_map);
end intrinsic;

/* Can't make this work (except by just doing a linear extension) 
   ... the FldFun/FldFunRat schism is absolutely bloody awful!!! 
intrinsic IsLocallySolvable(X::Sch, pl::RngUPol : completion_map:=0) -> BoolElt, Pt
{Tests local solubility of the scheme X (defined over a rational function field) at the place
 corresponding to the given ideal of the coordinate ring}
  
  require IsAffine(X) or IsProjective(X) : "Variety must be affine or projective";
  require Dimension(X) ge 1 and Dimension(Ambient(X)) ge 2 : 
         "Zero-dimensional schemes are not allowed, neither are ambient spaces";
  require IsIrreducible(X) and IsNonsingular(X) : 
         "Scheme should be irreducible and nonsingular";
  return IsLocallySolvable1(X, pl : completion_map:=completion_map);
end intrinsic; */

function IsLocallySolvable1(X, pl : completion_map:=0)
  K := BaseRing(X);  assert Type(K) eq FldFun and Type(BaseRing(K)) eq FldFunRat;
  t := K! BaseField(K).1;
  if completion_map cmpeq 0 then
     Kpl,m := Completion(K, pl);
  else
     m := completion_map;
     Kpl := Codomain(m);
  end if;
  k<aa>, res := ResidueClassField(Ideal(pl));
  resKpl := Inverse(m) * res;
  error if not Domain(m) cmpeq BaseRing(X), "m must be a base change map";

  Kp:=Codomain(m);  
  error if not ISA(Type(Kp),RngSer), "Codomain of m should be a local field";

  vprint LocSol: "Determining local solubility of ",X;
  
  // For affine varieties, convert to projective
  // (the code below would test for integral points on affine X)
  if IsAffine(X) then 
     ans, pt_proj := IsLocallySolvable(ProjectiveClosure(X), pl 
                                      : completion_map:=completion_map);
     pt := X(Ring(Parent(pt_proj)))! pt_proj;
     return ans, pt;
  end if;
  assert IsProjective(X);

  R:=IntegerRing(Kp);
  pi:=UniformizingElement(R);
  L:=BaseChangedDefiningEquations(X,m);
  RX:=PolynomialRing(R,Rank(Universe(L)));
  L:=[RX!ShiftVal(P,-Min([Valuation(c) : c in Coefficients(P)])):P in L];
  if IsAffine(X) then
    vprint LocSol: "Looking for *integral* points on the affine variety ...";
    IndentPush();
    /*
    if Dimension(X) eq -1 then return false,_;
    elif Dimension(X) eq 0 then
      vprint LocSol: "Using special routine for 0-dimensional scheme";
      V:=AllIntegralPoints(L,Minim([MinPrec(l):l in L]));
      bl:=not(IsEmpty(V));
      if bl then pt:=Rep(V); end if;
    else
      bl,pt:=HasIntegralPoints(L,Dimension(X));
    end if;
    */
    bl,pt:=HasIntegralPoints(L,Dimension(X),resKpl);
    IndentPop();
    if bl then
      vprint LocSol: "Found a point. Returning that";
      return true,PointSet(X,m)![Kp!u:u in pt];
    else
      return false,_;
    end if;
  elif IsProjective(X) then
    nvars := #Gradings(X)[1];
    num_vars_with_weight_gt_1 := #[ gg : gg in Gradings(X)[1] | gg gt 1 ];
    error if num_vars_with_weight_gt_1 gt 1, 
      "Not implemented for schemes in weighted projective space (except special cases)";
    if num_vars_with_weight_gt_1 eq 1 then
      _,j := Max(Gradings(X)[1]);  // the j'th variable is the special one
      one_at_j := [ (i eq j) select 1 else 0 : i in [1..nvars] ]; 
      bool := exists(kk){kk : kk in [1..#L] | Evaluate( L[kk], one_at_j) ne 0};
      if not bool then return true, PointSet(X,m)! one_at_j; end if;
      nj := Degree(L[kk], RX.j);
      cj := MonomialCoefficient(L[kk], RX.j^nj);
      // L[kk] contains a monomial cj*X_j^nj
      // Rescale, such that c has smaller valuation than the other coefficients.
      // (This implies that for any projective solution in which all coordinates 
      //  X_i (i ne j) are integral, the valuation of X_j is positive.)
      val_jth_coeff := Valuation( Evaluate( L[kk], one_at_j) );
      min_val_other_coeffs := Min([Valuation(c) : c in Coefficients(L[kk]-cj*RX.j^nj)]);
      if val_jth_coeff ge min_val_other_coeffs then
        // Rescaling is needed
        vprint LocSol: "Graded case: rescaling model";
        scaling := 1;
        scaled_vars := [ RX! (i eq j select 1 else pi) * RX.i : i in [1..nvars]];
        while val_jth_coeff ge min_val_other_coeffs do
          scaling *:= pi;
          L := [ Evaluate(P, scaled_vars) : P in L ];
          min_val_other_coeffs := Min([Valuation(c) : c in Coefficients(L[kk]-cj*RX.j^nj)]);
        end while;
        vprint LocSol: "Iterating over affine patches of rescaled projective variety ...";
        RXaff:=PolynomialRing(R,Rank(RX)-1);
        for i in [1..Rank(RX)] do
          if i eq j then continue; end if;
          patch:=[pi*RXaff.jj:jj in [1..i-1]] cat [1] cat [RXaff.jj: jj in [i..Rank(RXaff)]];
          vprint LocSol: "Looking on patch ",patch;
          IndentPush();        
          bl,pt:=HasIntegralPoints([Evaluate(P,patch):P in L], Dimension(X), resKpl);
          IndentPop();
          if bl then
            pt := [Kp!Evaluate(P,pt):P in patch];
            pt_scaled_back := [(ii eq j select 1 else scaling) * pt[ii] : ii in [1..nvars]];
            vprint LocSol: "Found point ", pt_scaled_back, "Returning that.";
            return true, PointSet(X,m)! pt_scaled_back;
          else
            vprint LocSol: "No point found.";
          end if;
        end for;
        return false,_;
      end if;
    end if;
    vprint LocSol: "Iterating over affine patches of projective variety ...";
    RXaff:=PolynomialRing(R,Rank(RX)-1);
    for i in [1..Rank(RX)] do
      patch:=[pi*RXaff.j:j in [1..i-1]] cat [1] cat [RXaff.j: j in [i..Rank(RXaff)]];
      vprint LocSol: "Looking on patch ",patch;
      IndentPush();        
      bl,pt:=HasIntegralPoints([Evaluate(P,patch):P in L], Dimension(X), resKpl);
      IndentPop();
      if bl then
        vprint LocSol: "Found point ",[Kp!Evaluate(P,pt):P in patch],"Returning that.";
        return true,PointSet(X,m)![Kp!Evaluate(P,pt):P in patch];
      else
        vprint LocSol: "No point found.";
      end if;
    end for;
    return false,_;
  else
    error "Wow, we've found a scheme that's neither affine nor projective.";
  end if;
end function;

