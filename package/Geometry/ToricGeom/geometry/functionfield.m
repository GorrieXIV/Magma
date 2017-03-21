freeze;

/////////////////////////////////////////////////////////////////////////
// functionfield.m
/////////////////////////////////////////////////////////////////////////
// $Revision: 26429 $
// $Date: 2010-05-04 12:15:40 +1000 (Tue, 04 May 2010) $
// $LastChangedBy: kasprzyk $
/////////////////////////////////////////////////////////////////////////
// Authors: Gavin Brown, Jaroslaw Buczynski, Alexander Kasprzyk
/////////////////////////////////////////////////////////////////////////


import "map.m": DefiningRationalFunctions, is_degree_zero;

declare attributes Sch:
   curve_in_stratum;        // the Crv object in the torus containing X.


declare attributes TorVar:
   function_field_map;      // the map from function field of X to field of
                            // fractions of its coordinate ring.
   
   
   
// returns the map from function field of X (a toric variety) to the field of
// fractions of coordinate ring of X. 
function get_function_field_map(X)
    if not assigned X`function_field_map then 
        _:=ToricFunctionField(X);
    end if;
    return X`function_field_map;
end function;


function get_curve_in_subtorus(X)
    if not assigned X`curve_in_stratum then 
        // THINK: these need fixing!
        error if not (IsReduced(X) and IsIrreducible(X)),
                "Curve error: Argument must reduced and irreducible";
        XinT, psi:=RestrictionToSubtorus(X); 
        // THINK: we require the dimension check after restricting to the 
        // subtorus, because Dimension currently does not work properly.
        error if  Dimension(X) ne 1,
                "Curve error: Argument must be a curve";
        X`curve_in_stratum:=Curve(XinT);
    end if;
    return X`curve_in_stratum;
end function;



intrinsic ToricFunctionField(X::Sch) -> Fld
{Function field of X, X must be a curve of an ambient}
    if ISA(Type(X), TorVar) then
        if not assigned X`function_field_map then 
            T, psi:=BigTorus(X);
            K:=FieldOfFractions(CoordinateRing(T));
            Q:=FieldOfFractions(CoordinateRing(X));
            phi:=hom<K -> Q | DefiningRationalFunctions(psi)>;
            X`function_field_map:=phi;
        end if;
        return Domain(X`function_field_map);
    end if;
    K:=FunctionField(get_curve_in_subtorus(X));
    F, mp:=AlgorithmicFunctionField(K);
    return F;
end intrinsic;


intrinsic ToricLiftRationalFunction(X::Sch, f::FldElt) -> FldElt
{Given a toric variety X or a curve X in a toric variety and a rational function
f on X (expressed in terms of the function field of X), returns f expressed in
terms of the coordinate ring of Ambient(X).}
     KX:=ToricFunctionField(X);
     require f in KX: "Argument 2 must be in function field of Argument 1.";
     if ISA(Type(X), TorVar) then
         phi:=get_function_field_map(X);
         return phi(f);
     end if;
     C:=X`curve_in_stratum;
     K:=FunctionField(C);
     _, mp:=AlgorithmicFunctionField(K);
     F:=FieldOfFractions(CoordinateRing(Ambient(C)));
     return ToricLiftRationalFunction(Ambient(C), Ambient(X),
                                                    F!Inverse(mp)(f));
end intrinsic;




intrinsic ToricLiftRationalFunction(X::TorVar, Y::TorVar, f::FldElt) -> FldElt
{Given a toric variety Y and its toric stratum X and a rational function f on X
(expressed in terms of the function field of X), returns a rational function on
Y (expressed in terms of the coordinate ring of Y), whose restriction to X is f}
     require BaseRing(X) cmpeq BaseRing(Y) : 
                                     "Arguments have different base rings.";
     KX:=ToricFunctionField(X);
     require f in KX: "Argument 3 must be in function field of Argument 1.";
     MY:=MonomialLattice(Y);
     MX:=MonomialLattice(X);
     if MY eq MX then 
         phi:=get_function_field_map(Y);
         return phi(f);
     end if;
     require IsSublattice(MX) : "Argument 1 must be a stratum of Argument 2"; 
     L, emb:=Superlattice(MX);
     require L eq MY : "Argument 1 must be a stratum of Argument 2"; 
     KY:=ToricFunctionField(Y);
     exps:=RowSequence(DefiningMatrix(emb));
     phi1:=hom< KX -> KY | [&*[Power(KY.i, expss[i])
                          : i in [1..#expss]]: expss in exps]>;
     phi2:=get_function_field_map(Y);
     return phi2(phi1(f));
end intrinsic;


intrinsic ToricRestrictRationalFunction(X::Sch, f::FldElt) -> FldElt
{If f is a rational function of degree 0 on ambient of X, returns f to }
     A:=Ambient(X);
     Q:=FieldOfFractions(CoordinateRing(A));
     require f in Q:
        "Argument 2 must be expressed in coordinates of ambient of Argument 1";
     require IsHomogeneous(A,f):
        "Argument must be homogeneous";
     require is_degree_zero(A,f):
        "Argument must have total degree 0";
     F:=ToricFunctionField(X);
     if ISA(Type(X) , TorVar) then
         _, psi:=BigTorus(X);
         return RationalFunction(psi*f);
     end if;
     XinT, psi:=RestrictionToSubtorus(X); 
     ff:=RationalFunction(psi*f);
     C:=get_curve_in_subtorus(X);
     K:=FunctionField(C);
     _, mp:=AlgorithmicFunctionField(K);
     return mp(K!ff);
end intrinsic;




intrinsic GeometricGenusUsingToricGeometry(C::Sch) -> RngIntElt
{The geometric genus of C, C must be a curve}
    C:=get_curve_in_subtorus(C);
    return GeometricGenus(C);
end intrinsic;




