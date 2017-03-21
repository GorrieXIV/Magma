freeze;

////////////////////////////////////////////////////////////////////////
//                                                                    // 
//                     ALTERNATE MODELS FOR CONICS                    //  
//                            David Kohel                             // 
//                                                                    // 
//////////////////////////////////////////////////////////////////////// 

intrinsic LegendreModel(C1::CrvCon) -> CrvCon, MapIsoSch
    {A diagonalized or Legendre model aX^2+bY^2+cZ^2 for a conic,
    followed by the isomorphism.}
    PP := Ambient(C1);
    require Characteristic(BaseRing(PP)) ne 2 :
      "A Legendre model exists only in characteristic different from 2.";
    f0, M0 := LegendrePolynomial(C1);
    C0 := Conic(PP,f0);
    M1 := Adjoint(M0);
    eqns0 := [ &+[ M0[i,j]*PP.i : i in [1..3] ] : j in [1..3] ];
    eqns1 := [ &+[ M1[i,j]*PP.i : i in [1..3] ] : j in [1..3] ]; 
    return C0, iso< C1 -> C0 | eqns1, eqns0 >;
end intrinsic;

intrinsic ReducedLegendreModel(C1::CrvCon) -> CrvCon, MapIsoSch
    {A reduced Legendre model aX^2+bY^2+cZ^2 for a conic over Q, with 
    a, b, and c pairwise coprime, followed by the isomorphism.}
    PP := Ambient(C1);
    require Type(BaseRing(PP)) in {FldRat,RngInt} :
      "A reduced Legendre model exists only over Q or Z.";
    f0, M0 := ReducedLegendrePolynomial(C1);
    C0 := Conic(PP,f0);
    M1 := Adjoint(M0);
    eqns0 := [ &+[ M0[i,j]*PP.i : i in [1..3] ] : j in [1..3] ];
    eqns1 := [ &+[ M1[i,j]*PP.i : i in [1..3] ] : j in [1..3] ]; 
    return C0, iso< C1 -> C0 | eqns1, eqns0 >;
end intrinsic;

function QFToMatrix(Q) P:=Parent(Q);
 BR:=BaseRing(P); FF:=FieldOfFractions(BR); C:=Coefficient; r:=Rank(P);
 M:=[[i ne j select FF!BR!C(C(Q,i,1),j,1)/2
 else FF!BR!C(Q,i,2) : i in [1..r]] : j in [1..r]];
 return Matrix(r,r,M); end function;

intrinsic IsDefinedByQuadric(X::Sch) -> BoolElt,AlgMatElt
{Determine if a projective scheme is defined by a single quadric equation}
 if not IsProjective(X) then return false,_; end if;
 D:=DefiningEquations(X); if #D ne 1 then return false,_; end if;
 if TotalDegree(D[1]) ne 2 then return false,_; end if; 
 require Characteristic(BaseRing(X)) ne 2: "Characteristic must not be 2";
 return true,QFToMatrix(D[1]); end intrinsic;

intrinsic IsDefinedByQuadrics(X::Sch) -> BoolElt,SeqEnum
{Determine if a projective scheme is defined by quadric equations}
 if not IsProjective(X) then return false,_; end if; D:=DefiningEquations(X);
 for d in D do if TotalDegree(D[1]) ne 2 then return false,_; end if; end for;
 require Characteristic(BaseRing(X)) ne 2: "Characteristic must not be 2";
 return true,[QFToMatrix(x) : x in D]; end intrinsic;
