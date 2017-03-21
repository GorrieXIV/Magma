/*
  Intrinsics for classical groups not documented in the Magma Handbook 
  (version 2.19)

  Don Taylor (2013-07-04)

  $Id: variants.m 43900 2013-07-16 02:57:11Z don $

  History:
    1) Intrinsics which take a matrix F representing a form
       Moved from conformal.m on 2013-07-04
       
    2) Generic forms for orthogonal groups Name(t,d,F) where t is -1, 0 or 1
       Moved from group.m on 2013-07-09
*/

// ========================================================
//
// Groups defined by forms
//

intrinsic ConformalUnitaryGroup( F::Mtrx ) -> GrpMat
{The conformal unitary group preserving the form with matrix F}
    K := BaseRing(F);
    n := Nrows(F);
    require n eq Ncols(F) : "Form matrix must be square";
    // should check form
    G := ConformalUnitaryGroup(n, K);
    S := UnitaryForm(n, K);
    if S eq F then
        return G;
    else
        T := TransformForm(F,"unitary");
        return G^(T^-1);
    end if;
end intrinsic;

intrinsic ConformalSymplecticGroup( F::Mtrx ) -> GrpMat
{The conformal symplectic group preserving the form with matrix F}
    K := BaseRing(F);
    n := Nrows(F);
    require n eq Ncols(F) : "Form matrix must be square";
    // should check form
    G := ConformalSymplecticGroup(n, K);
    if F eq StandardAlternatingForm(n, K);
        return G;
    else
        T := TransformForm(F,"symplectic");
        return G^(T^-1);
    end if;
end intrinsic;

intrinsic ConformalOrthogonalGroupPlus( F::Mtrx ) -> GrpMat
{The conformal orthogonal group COPlus(F) preserving the form with matrix F}
    K := BaseRing(F);
    n := Nrows(F);
    require n eq Ncols(F) : "Form matrix must be square";
    // should check form
    G := ConformalOrthogonalGroupPlus(n, K);
    S := QuadraticFormPlus(n, K);
    if S eq F then
        return G;
    else
        T := TransformForm(F,"orthogonalplus");
        return G^(T^-1);
    end if;
end intrinsic;

intrinsic ConformalOrthogonalGroupMinus( F::Mtrx ) -> GrpMat
{The conformal orthogonal group COMinus(F) preserving the form with matrix F}
    K := BaseRing(F);
    n := Nrows(F);
    require n eq Ncols(F) : "Form matrix must be square";
    // should check form
    G := ConformalOrthogonalGroupMinus(n, K);
    S := QuadraticFormMinus(n, K);
    if S eq F then
        return G;
    else
        T := TransformForm(F,"orthogonalminus");
        return G^(T^-1);
    end if;
end intrinsic;

intrinsic ConformalOrthogonalGroup( F::Mtrx ) -> GrpMat
{The conformal orthogonal group CO(F) preserving the form with matrix F}
    K := BaseRing(F);
    n := Nrows(F);
    require n eq Ncols(F) : "Form matrix must be square";
    // should check form
    G := ConformalOrthogonalGroup(n, K);
    S := QuadraticForm(n, K);
    if S eq F then
        return G;
    else
        T := TransformForm(F,"orthogonalcircle");
        return G^(T^-1);
    end if;
end intrinsic;


// ========================================================
//
// Generic conformal groups
//


// return T st T*F1*Tr(T) eq F2
// where Fi is the square matrix of degree 2*m+1 with
// 1s on the antidiagonal, except for Fi[m+1,m+1] = ai (i=1,2).
centreTransformer := function( m, F, a1, a2 )
    c := a2/a1;
    if IsSquare( c ) then
        c0 := F!1;  c1 := Sqrt(c);
    else
        c0 := Nonsquare(F);  c1 := Sqrt(c*c0);
    end if;
    I := IdentityMatrix(F,m);
    return DiagonalJoin(c0*I,DiagonalJoin(Matrix(1,1,[c1]),I));
end function;

intrinsic ConformalOrthogonalGroup( t::RngIntElt, n::RngIntElt, F::FldFin ) -> GrpMat
{The matrix group CO^t(V) where V is K^n, K is F_q, t in 0, +1 or -1.}
    require IsFinite(F) : "The field must be finite";
    if IsEven(n) then
        require t in [+1,-1] : "Invalid sign";
        return (t eq +1) select COPlus(n,F) else COMinus(n,F);
    else
        require t in [+1,0,-1] : "Invalid sign";
        if Characteristic(F) eq 2 then
            require t eq 0 : "Invalid sign";
        end if;
        G := CO(n,F);
        gord := FactoredOrder(G);
        G := sub< Generic(G) | [ Transpose(G.i^-1) : i in [1..Ngens(G)] ] >;
        if t ne 0 then
            c := (t eq +1) select F!1/2 else Nonsquare(F)/2;
            if IsSquare( c ) then
                c0 := F!1;  c1 := Sqrt(c);
            else
                c0 := Nonsquare(F);  c1 := Sqrt(c*c0);
            end if;
            T := centreTransformer( n div 2, F,
              F!2, (t eq +1) select F!1 else Nonsquare(F) );
            G := sub< Generic(G) | [ T*G.i*T^-1 : i in [1..Ngens(G)] ] >;
        end if;
        G`Order := gord;
        return G;
    end if;
end intrinsic;

intrinsic ConformalOrthogonalGroup( t::RngIntElt, n::RngIntElt, q::RngIntElt ) -> GrpMat
{The matrix group CO^t(V) where V is K^n, K is F_q, t in 0, +1 or -1.}
    return ConformalOrthogonalGroup(t,n,GF(q));
end intrinsic;

intrinsic ConformalOrthogonalGroup( t::RngIntElt, V::ModTupFld ) -> GrpMat
{The matrix group CO^t(V) where t is one of 0, +1 or -1.}
    d := Dimension(V);  K := BaseRing(V);
    require d gt 0 : "Invalid dimension -- should be positive";
    return ConformalOrthogonalGroup(t,d,K);
end intrinsic;

intrinsic ConformalClassicalGroup( F::Mtrx, type::MonStgElt ) -> GrpMat
{The conformal classical group preserving the form F up to scalars}
    d := Nrows(F);  K := BaseRing(F);
    case type :
        when "linear" : return GL(d,K);
        when "unitary" : return CU(F);
        when "symplectic" : return CSp(F);
        when "orthogonal" : return CO(F);
    end case;
end intrinsic;

// ========================================================
//
// Unitary groups
//
intrinsic GeneralUnitaryGroup( F::Mtrx ) -> GrpMat
{The general unitary group GU(F) preserving the form with matrix F}
    K := BaseRing(F);
    n := Nrows(F);
    require n eq Ncols(F) : "Form matrix must be square";
    // should check form
    G := GeneralUnitaryGroup(n, K);
    S := UnitaryForm(n, K);
    if S eq F then
        return G;
    else
        T := TransformForm(F,"unitary");
        return G^(T^-1);
    end if;
end intrinsic;

intrinsic SpecialUnitaryGroup( F::Mtrx ) -> GrpMat
{The special unitary group GU(F) preserving the form with matrix F}
    K := BaseRing(F);
    n := Nrows(F);
    require n eq Ncols(F) : "Form matrix must be square";
    // should check form
    G := SpecialUnitaryGroup(n, K);
    S := UnitaryForm(n, K);
    if S eq F then
        return G;
    else
        T := TransformForm(F,"unitary");
        return G^(T^-1);
    end if;
end intrinsic;

// ========================================================
//
// Generic Omega groups
//
intrinsic Omega( t::RngIntElt, n::RngIntElt, F::FldFin ) -> GrpMat
{The matrix group Omega^t(V) where V is K^n, K is F_q, t in 0, +1 or -1.}
    require IsFinite(F) : "The field must be finite";
    if IsEven(n) then
        require t in [+1,-1] : "Invalid sign";
        return (t eq +1) select OmegaPlus(n,F) else
            OmegaMinus(n,F);
    else
        require t in [+1,0,-1] : "Invalid sign";
        if Characteristic(F) eq 2 then
            require t eq 0 : "Invalid sign";
        end if;
        G := Omega(n,F);
        G := sub< Generic(G) | [ Transpose(G.i^-1) : i in [1..2] ] >;
        // we should not need to do this
        /*if t ne 0 then
          c := (t eq +1) select F!1/2 else Nonsquare(F)/2;
          if IsSquare( c ) then
              c0 := F!1;  c1 := Sqrt(c);
          else
              c0 := Nonsquare(F); c1 := Sqrt(c*c0);
          end if;
          m := (n div 2) +1;
          G := sub< Generic(G) | [ c0*MultiplyColumn(MultiplyRow(G.i,c1,m),c1^-1,m)
            : i in [1..2] ] >;
        end if;*/
        return G;
    end if;
end intrinsic;

intrinsic Omega(t::RngIntElt, d::RngIntElt, q::RngIntElt) -> GrpMat
{The matrix group Omega^t(d,K)}
  return Omega(t,d,GF(q));
end intrinsic;

intrinsic Omega(t::RngIntElt, V::ModTupFld) -> GrpMat
{The matrix group Omega^t(V)}
  d := Dimension(V);  K := BaseRing(V);
  require d gt 0 : "Invalid dimension -- should be positive";
  require IsEven(d) : "Invalid dimension -- should be even";
  return Omega(t,d,K);
end intrinsic;

// ========================================================
//
// Generic orthogonal groups
//
intrinsic GeneralOrthogonalGroup( t::RngIntElt, n::RngIntElt, F::FldFin ) -> GrpMat
{The matrix group GO^t(V) where V is K^n, K is F_q, t in 0, +1 or -1.}
   require IsFinite(F) : "The field must be finite";
  if IsEven(n) then
    require t in [+1,-1] : "Invalid sign";
    return (t eq +1) select GOPlus(n,F) else
      GOMinus(n,F);
  else
     require t in [+1,0,-1] : "Invalid sign";
     if Characteristic(F) eq 2 then
       require t eq 0 : "Invalid sign";
     end if;
     G := GO(n,F);
     return sub< Generic(G) | [ Transpose(G.i^-1) : i in [1..2] ] >;
     /*if sign ne 0 then
       m := n div 2;
       F[m+1,m+1] := (sign eq 1) select F!1/2 else Nonsquare(F)/2;
     end if;
     return F;*/
  end if;
end intrinsic;

intrinsic GeneralOrthogonalGroup( t::RngIntElt, n::RngIntElt, q::RngIntElt ) -> GrpMat
{The matrix group GO^t(V) where V is K^n, K is F_q, t in 0, +1 or -1.}
  return GeneralOrthogonalGroup(t,n,GF(q));
end intrinsic;

intrinsic GeneralOrthogonalGroup( t::RngIntElt, V::ModTupFld ) -> GrpMat
{The matrix group GO^t(V) where V is K^n, K is F_q, t in 0, +1 or -1.}
  return GeneralOrthogonalGroup(t,V);
end intrinsic;

intrinsic SpecialOrthogonalGroup( t::RngIntElt, n::RngIntElt, F::FldFin ) -> GrpMat
{The matrix group SO^t(V) where V is K^n, K is F_q, t in 0, +1 or -1.}
   require IsFinite(F) : "The field must be finite";
  if IsEven(n) then
    require t in [+1,-1] : "Invalid sign";
    return (t eq +1) select SOPlus(n,F) else
      SOMinus(n,F);
  else
     require t in [+1,0,-1] : "Invalid sign";
     if Characteristic(F) eq 2 then
       require t eq 0 : "Invalid sign";
     end if;
     G := SO(n,F);
     return sub< Generic(G) | [ Transpose(G.i^-1) : i in [1..2] ] >;
     /*if sign ne 0 then
       m := n div 2;
       F[m+1,m+1] := (sign eq 1) select F!1/2 else Nonsquare(F)/2;
     end if;
     return F;*/
  end if;
end intrinsic;

intrinsic SpecialOrthogonalGroup( t::RngIntElt, n::RngIntElt, q::RngIntElt ) -> GrpMat
{The matrix group SO^t(V) where V is K^n, K is F_q, t in 0, +1 or -1.}
  return SpecialOrthogonalGroup(t,n,GF(q));
end intrinsic;

intrinsic SpecialOrthogonalGroup( t::RngIntElt, V::ModTupFld ) -> GrpMat
{The matrix group SO^t(V) where V is K^n, K is F_q, t in 0, +1 or -1.}
  return SpecialOrthogonalGroup(t,V);
end intrinsic;

