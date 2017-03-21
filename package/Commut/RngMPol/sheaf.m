freeze;

import "dual2.m" : MyHilbertSeries, MyHilbertPolynomial;
import "../../Geometry/Srfc/kod_enr.m" : h0;

declare type ShfCoh;
declare attributes ShfCoh:
    M,		//  ModMPol - polynomial module representing sheaf F
    X,		//  Sch - ordinary projective scheme on which F lies
    Mtype,	//  RngIntElt - unnecessary!
    Isupp,	//  RngMPol - defining ideal of X
    Iann,	//  RngMPol - exact annihilator of F >= Isupp 
    Mfull,	//  ModMPol - a maximal module representing F
    M0,		//  ModMPol - a maximal module representing F in degrees >=0
    /////////////////////////////////////////////////
    // R-R/Divisor map data for invertible sheaves //
    div_map,	//  MapSchGrph - the divisor map of F, if F is an invertible sheaf
    rr_space,	//  Tup - Riemann-Roch as polys + denominator
    ////////////////////////////////////////////
    // Module over Noether Normalisation data //
    Mprj,	//  ModMPol - M or Mfull as a module over a noether norm subring
    xmats,	//  SeqEnum - mats representing mult by xi on Mprj
    xmap,	//  Map - (inverse of) coord change map for noether subring
    prj_is_full,//  BoolElt - is Mprj for Mfull or just M?
    /////////////////////
    // Some Attributes //
    loc_free_rk,//  RngIntElt - r, if sheaf loc. free rank r, else -1
    is_arith_CM;//  BoolElt   - true iff sheaf is arithmetically CM

declare type ShfHom;
declare attributes ShfHom:
    dom,	//  SchCoh - the sheaf domain
    cod,	//  SchCoh - the sheaf codomain
    r1,		//  RngIntElt - rep mod dom : 0=M, 1 = Mfull, 2 = M0
    r2,		//  RngIntElt - rep mod cod : 0=M, 1 = Mfull, 2 = M0
    hm,		//  ModMPolHom - the actual underlaying module map
    deg;	//  RngIntElt - twist s.t. hom : dom -> cod(deg)

///////////////// HackObj Basic ShfCoh intrinsics /////////////////////

intrinsic Print(x::ShfCoh, level::MonStgElt)
{}
    case level:
	when "Minimal":
	  printf "Coherent sheaf on ";
	  x`X:Minimal;
	  return;
	when "Maximal":
	  ful := assigned x`Mfull;
	  printf "Coherent sheaf with";
	  if ful then printf " (maximal)"; end if;
	  printf " underlying module\n";
	  ful select x`Mfull else x`M;
	  printf "\non scheme\n";
	  x`X:Maximal;
	  return;
    end case;
    // default
    printf "Coherent sheaf on ";
    x`X:Minimal;
end intrinsic;

intrinsic Print(x::ShfHom, level::MonStgElt)
{}
    case level:
	when "Minimal":
	  print "Sheaf homomorphism.";
	  return;
	when "Maximal":
	  printf "Sheaf homomorphism from sheaf\n";
	  x`dom:Maximal; printf "\n";
	  printf "to sheaf\n";
	  x`cod:Maximal; printf "\n";
	  printf "defined by module homomorphism\n";
	  x`hm:Maximal;
	  return;
    end case;
    // default
    printf "Sheaf homomorphism defined by module homomorphism\n";
    x`hm;

end intrinsic;

intrinsic IsCoercible(x::ShfCoh, y::.) -> BoolElt,.
{}
    return false, "Illegal coercion";
end intrinsic;

intrinsic IsCoercible(x::ShfHom, y::.) -> BoolElt,.
{}
    return false, "Illegal coercion";
end intrinsic;

intrinsic 'in'(x::., y::ShfCoh) -> BoolElt
{}
    return false;
end intrinsic;

intrinsic 'in'(x::., y::ShfHom) -> BoolElt
{}
    return false;
end intrinsic;

//////////////////////////////////////////////////
function QuotientIdealBasis(I,J,n)
// finds a basis for degree n part of I/J, I >= J homog. ideals
    
    P := Generic(I);
    Mons_n := Setseq(MonomialsOfDegree(P,n));
    V := KSpace(BaseRing(P),#Mons_n);
    
    //subspace of V corr to I
    Ivecs := [V|];
    B := Basis(I);
    for b in B do
        d := LeadingTotalDegree(b);
        if d gt n then continue; end if;
        Monoms := MonomialsOfDegree(P,n-d);
        Ivecs cat:= [V![MonomialCoefficient(e,m):m in Mons_n] where
		e is b*m :m in Monoms];
   end for;
   WI := sub<V|Ivecs>;
   delete Ivecs;

    //subspace of V corr to J
    Jvecs := [V|];
    B := Basis(J);
    for b in B do
        d := LeadingTotalDegree(b);
        if d gt n then continue; end if;
        Monoms := MonomialsOfDegree(P,n-d);
        Jvecs cat:= [V![MonomialCoefficient(e,m):m in Mons_n] where
		e is b*m :m in Monoms];
   end for;
   WJ := sub<V|Jvecs>;
   delete Jvecs;

   WImodJ := Complement(WI,WJ);
   B := [Polynomial(Eltseq(f),Mons_n) : f in Basis(WImodJ)];
   return B;
    
end function;

function SpecialHilbertSeries(F)
// The Hilbert Series of the graded free module F=R(r1)+..+R(rm)
    R := BaseRing(F);
    wts := ColumnWeights(F);
    P := RationalFunctionField(Integers()); t := P.1;
    if #wts eq 0 then return P!0; end if;
    wm := Min(wts); r := Rank(R);
    return ((t^wm)*&+[t^(w-wm) : w in wts])/((1-t)^r);
end function;

///////////// Creation and Twist functions /////////////////////////////

intrinsic Sheaf(M::ModMPol, X::Sch) -> ShfCoh
{ Create the coherent sheaf on X represented by graded module M }
    require IsOrdinaryProjective(X):
	"Sheaves currently only for ordinary projective schemes";
    R := CoordinateRing(Ambient(X));
    require BaseRing(M) eq R:
	"M must be a module for the coordinate ring of the ambient of X";
    Saturate(~X);
    I := Ideal(X);
    require IsHomogeneous(M):
	"M must be a homogeneous module";
    I1 := Saturation(Annihilator(M));
    require I subset I1:
	"M doesn't give a sheaf supported on X";

    /* Warning: handle reduced and embedded properly! */
    S := New(ShfCoh);
    S`M := M; S`X := X; S`Isupp := I; S`Iann := I1;
    return S;

end intrinsic;

intrinsic CanonicalSheaf(X::Sch,d::RngIntElt) -> ShfCoh 
{ Create the dth Serre twist of the canonical sheaf on (equidimensional, 
  locally Cohen-Macaulay) scheme X }
    require IsOrdinaryProjective(X):
	"Sheaves currently only for ordinary projective schemes";

    if assigned X`KX then
	KX := X`KX;
	return (d eq 0) select KX else Twist(KX,d);
    end if;
    Saturate(~X);
    I := Ideal(X);
    KX,bsat := CanonicalModule(I);
    S := New(ShfCoh);
    S`M := KX; S`X := X; S`Isupp := I; S`Iann := I;
    /* Warning: Check Iann := I!! */
    if d ne 0 then Sd := Twist(S,d); end if;
    if bsat then
	S`Mfull := KX;
	if d ne 0 then Sd`Mfull := Sd`M; end if;
    end if;
    X`KX := S;
    if d eq 0 then
        return S;
    else
	return Sd;
    end if;

end intrinsic;

intrinsic CanonicalSheaf(X::Sch) -> ShfCoh 
{ Create the the canonical sheaf on (equidimensional, locally Cohen-Macaulay)
  scheme X }
    require IsOrdinaryProjective(X):
	"Sheaves currently only for ordinary projective schemes";
    return CanonicalSheaf(X,0);
end intrinsic;

intrinsic StructureSheaf(X::Sch, n::RngIntElt) -> ShfCoh
{ Create the twisted structure sheaf O_X(n) on scheme X }
    require IsOrdinaryProjective(X):
	"Sheaves currently only for ordinary projective schemes";

    Saturate(~X);
    I := Ideal(X);
    R := Generic(I);
    M := quo<RModule(R,[-n])|[[b] : b in Basis(I)]>;
    S := New(ShfCoh);
    S`M := M; S`X := X; S`Isupp := I; S`Iann := I;
    return S;

end intrinsic;

intrinsic StructureSheaf(X::Sch) -> ShfCoh
{ Create the structure sheaf O_X on scheme X }
    require IsOrdinaryProjective(X):
	"Sheaves currently only for ordinary projective schemes";
    return StructureSheaf(X,0);
end intrinsic;

intrinsic Twist(S::ShfCoh,d::RngIntElt) -> ShfCoh
{ Create the Serre twist S(d) of sheaf S }
    if d eq 0 then return S; end if;
    M := Twist(S`M,d);
    Sd := New(ShfCoh);
    Sd`M := M; Sd`X := S`X; Sd`Isupp := S`Isupp;
    if assigned S`Iann then Sd`Iann := S`Iann; end if;
    if assigned S`Mfull then Sd`Mfull := Twist(S`Mfull,d); end if;
    if assigned S`Mprj then
	Sd`Mprj := Twist(S`Mprj,d); Sd`xmats := S`xmats;
	Sd`xmap := S`xmap; Sd`prj_is_full := S`prj_is_full;
    end if;
    if assigned S`loc_free_rk then 
	Sd`loc_free_rk := S`loc_free_rk;
    end if;
    if assigned S`is_arith_CM then 
	Sd`is_arith_CM := S`is_arith_CM;
    end if;
    return Sd;
end intrinsic;

intrinsic Restriction(S::ShfCoh, Y::Sch : Check := true) -> ShfCoh
{ Restriction of S to subscheme Y of the base scheme of S }
    if Check then
	require Y subset S`X:
	  "Second argument must be a subscheme of the base scheme of the first";
    end if;
    M := (assigned S`Mfull) select S`Mfull else S`M;
    Saturate(~Y);
    IY := Ideal(Y);
    wts := ColumnWeights(M);
    F := RModule(Generic(IY),wts);
    M1 := quo<F|[F!r : r in Relations(M)] cat [b*(F.i) : i in [1..Rank(F)],
				b in Basis(IY)]>;
    SY := New(ShfCoh);
    SY`M := M1; SY`X := Y; SY`Isupp := IY;
    return SY;

end intrinsic;

intrinsic SheafOfDifferentials(X::Sch : Maximize := false) -> ShfCoh
{ Return the sheaf of differentials on ordinary projective scheme X}
    require IsOrdinaryProjective(X):
	"Sheaves currently only for ordinary projective schemes";
    P := Ambient(X);
    R := CoordinateRing(P);
    // Get appropriate terms in Koszul complex.
    // Omega^1_{P/k} is isomorphic to the image of the last
    // map in this exact section of the Koszul complex:
    //  R^(n choose 3) -> R^(n choose 2) -> R^n
    // where n=Dim(P)+1
    n := Rank(R);
    F := Module(R,[1: i in [1..n]]);
    mat := ZeroMatrix(R,Binomial(n,2),n);
    pairs := [[i,j] : j in [i+1..n],i in [1..n]];
    for i in [1..#pairs] do
	p := pairs[i];
	mat[i,p[1]] := -R.(p[2]); mat[i,p[2]] := R.(p[1]);
    end for;
    Saturate(~X);
    B := MinimalBasis(Ideal(X));

    if #B gt 0 then
        F1 := Module(R,[2: i in [1..#pairs]]);;
        M := quo<F|[F![Derivative(f,i) : i in [1..n]] : f in B] cat
		[b*F.i : i in [1..n], b in B]>;
        mp := Homomorphism(F1,M,mat : Check := false);
	rels := Kernel(mp);
	Omega := quo<F1|rels>;
        Omega := Presentation(Omega); //get to reduced form
	//M1 := QuotientModule(Ideal(X));
	//mp := Homomorphism(M,M1,Matrix(R,n,1,[R.i : i in [1..n]]) : Check := false);
	//Omega := Kernel(mp);
    else
        Omega := sub<F|[F!r:r in RowSequence(mat)]>; //differential module of P 
	Omega := Presentation(Omega);
    end if;
    if Maximize and (#B gt 0) then
	Omega := ModuleSaturation(Omega);
    end if;

    S := New(ShfCoh);
    S`M := Omega; S`X := X; S`Isupp := Ideal(X);
    S`Iann := Ideal(X); // do properly!
    if Maximize or (#B eq 0) then
	S`Mfull := Omega;
    end if;
    return S;
    
end intrinsic;

intrinsic TangentSheaf(X::Sch : Maximize := false) -> ShfCoh
{ Return the locally-free tangent sheaf on ordinary projective scheme X}
    require IsOrdinaryProjective(X):
	"Sheaves currently only for ordinary projective schemes";
    P := Ambient(X);
    R := CoordinateRing(P);
    n := Rank(R);
    Saturate(~X);
    B := MinimalBasis(Ideal(X));
    B1 := [b : b in DefiningPolynomials(X)| b ne 0];
    if #B lt #B1 then B1 := B; end if;
    if #B1 gt 0 then
	mat := Transpose(Matrix(R,[[Derivative(f,i) : i in [1..n]] : f in B1]));
	M1 := quo<F|[F![R.i : i in [1..n]]] cat [b*F.i : i in [1..n], b in B]>
		where F is Module(R,[-1: i in [1..n]]);
	F2 := Module(R,[LeadingTotalDegree(b) : b in B1]);
	M2 := quo<F2| [b*F2.i : i in [1..#B1], b in B]>;
	mp := Homomorphism(M1,M2,mat : Check := false);
	TanS := Kernel(mp);
	TanS := Presentation(TanS);
    else
	TanS := quo<F|[F![R.i : i in [1..n]]]> where
		 F is RModule(R,[-1: i in [1..n]]);
    end if;
    if Maximize and ((#B1 gt 0) or (Dimension(P) eq 1)) then
	TanS := ModuleSaturation(TanS);
    end if;

    S := New(ShfCoh);
    S`M := TanS; S`X := X; S`Isupp := Ideal(X);
    S`Iann := Ideal(X); // do properly!
    if Maximize or ((#B1 eq 0) and (Dimension(P) gt 1)) then
	S`Mfull := TanS;
    end if;
    return S;

end intrinsic;

intrinsic HorrocksMumfordBundle(P::Prj) -> ShfCoh
{ P is ordinary projective 4-space over a field. Returns the sheaf giving
  the rank 2 locally free Horrocks-Mumford bundle on P }

    require IsAmbient(P) and IsOrdinaryProjective(P) and
	(Dimension(P) eq 4) and IsField(BaseRing(P)) :
	"P must be 4-dimensional projective space over a field";
    R := CoordinateRing(P);
    x0,x1,x2,x3,x4 := Explode([R.i : i in [1..5]]);
    rels := [
    [x0*x2,x1^2,-x3*x4,0,-x1,0,0,x2,0,x0,0,0,0,0,0,0,0,0,0],
    [x2*x3,0,0,0,0,x1,0,0,x2,x3,x4,0,0,0,0,0,0,0,0],
    [-x3^2,0,0,x2*x4,-x0,0,0,0,-x3,0,0,0,0,0,-x1,0,0,0,0],
    [-x4^2,0,0,x0*x3,-x2,0,x1,0,0,0,0,x4,0,0,0,0,0,0,0],
    [0,0,0,0,0,x3,-x0,0,0,0,0,0,0,-x4,-x2,0,0,0,0],
    [0,x1*x3,x2^2,0,-x3,-x0,0,0,0,0,0,0,0,0,0,0,0,0,0],
    [0,x2*x3,0,-x1*x4,0,0,-x3,-x0,0,0,0,0,0,0,0,x2,0,0,0],
    [0,x4^2,-x1*x2,0,0,0,0,x3,-x0,0,0,0,-x4,0,0,0,0,0,0],
    [0,0,x0*x4,0,0,0,-x2,0,x1,0,0,0,0,0,0,0,0,0,-x3],
    [0,0,0,-x3^2,0,-x2,0,x1,0,0,0,0,0,0,0,0,0,0,0],
    [x0*x4,0,0,x2^2,0,0,0,0,0,0,0,-x0,0,x1,0,0,0,0,0],
    [x3*x4,0,0,x1^2,0,0,0,0,0,0,0,-x3,0,0,0,0,x2,0,0],
    [0,-x1*x4,-x0^2,0,x4,0,0,0,0,0,0,0,0,x2,0,0,0,0,0],
    [0,0,0,0,x4,0,0,0,0,0,0,0,-x1,x2,0,0,0,x3,0],
    [0,-x2*x4,0,0,0,0,x4,0,0,0,-x0,0,x2,0,0,0,-x1,0,0],
    [0,0,-x3^2,0,0,0,-x4,0,0,0,0,0,0,0,0,0,x1,0,0],
    [0,0,-x0*x3,x1*x2,0,-x4,0,0,0,0,0,0,0,0,0,0,0,0,0],
    [0,0,0,x2^2,0,0,0,-x4,0,0,-x3,0,0,0,0,0,0,0,0],
    [0,0,0,0,0,0,0,0,-x4,0,0,-x3,0,0,0,0,x2,x0,0],
    [0,0,x2*x3,0,0,0,0,0,0,0,0,-x1,0,0,x0,0,0,0,-x4],
    [0,0,x0*x2,-x3*x4,0,0,0,0,0,0,-x1,0,0,0,0,0,0,0,0],
    [0,0,0,x4^2,0,0,0,0,0,-x1,0,0,0,x0,0,0,0,0,0],
    [0,0,0,x1*x3,0,0,0,0,0,x2,0,0,-x0,0,-x4,0,0,0,0],
    [0,0,-x0*x1,0,0,0,0,0,0,x4,0,x2,0,0,0,-x3,0,0,0],
    [0,0,-x4^2,0,0,0,0,0,0,0,-x2,0,0,0,0,x0,0,0,0],
    [0,0,-x1*x4,x2*x3,0,0,0,0,0,0,0,0,0,0,0,0,-x0,0,0],
    [0,0,x2^2,0,0,0,0,0,0,0,0,0,0,0,0,-x1,-x4,0,0],
    [0,0,-x1^2,0,0,0,0,0,0,0,0,0,0,x4,x2,0,0,0,0],
    [0,0,0,x3^2,0,0,0,0,0,0,0,0,0,0,0,0,0,-x4,-x0],
    [0,0,0,x0^2,0,0,0,0,0,-x3,-x4,0,0,0,0,0,0,0,0],
    [0,0,-x2*x4,x0*x1,0,0,0,0,0,0,0,0,0,-x3,0,0,0,0,0],
    [0,0,-x4^2,0,0,0,0,0,0,0,0,0,0,0,x3,0,0,-x1,0],
    [0,0,0,x0*x2,0,0,0,0,0,0,0,0,-x3,0,0,-x4,0,0,x1],
    [0,0,-x1*x3,x0*x4,0,0,0,0,0,0,0,0,0,0,0,0,0,x2,0],
    [0,0,0,-x4^2,0,0,0,0,0,0,0,0,0,0,0,0,-x3,0,x2] ];
    F := RModule(R,[0,0,0,0] cat [1 : i in [1..15]]);
    M := quo<F|[F!r : r in rels]>;

    S := New(ShfCoh);
    I := ideal<R|>;
    S`M := M; S`X := P; S`Isupp := I; S`Iann := I;
    S`Mfull := M; S`loc_free_rk := 2; S`is_arith_CM := false;
    return S;

end intrinsic;

///////////////// Some accessor functions /////////////////////////

function TruncateToWeights(M,d)
    wts := ColumnWeights(M);
    adjs := [d-wt: wt in wts];
    R := BaseRing(M);
    if Max(adjs) le 0 then return M; end if;

    gens := [];
    n := Rank(R); m := #wts;
    for i in [1..m] do
	r := Max(adjs[i],0);
	st := [R|0:j in [1..i-1]]; fin := [R|0:j in [i+1..m]];
	gens cat:= [st cat [f] cat fin : f in MonomialsOfDegree(R,r)];
    end for;
    M1 := sub<M|gens>;
    M1 := quo<M1|>; // temp fix for minimisation!
    return M1;
end function;

function GlobalSecSubmod(M)
    wts := ColumnWeights(M);
    cols := [i : i in [1..#wts] | wts[i] eq 0];
    if #cols eq 0 then return M; end if;
    R := BaseRing(M);
    vecs := [[R!0 : i in [1..#wts]] : j in [1..#cols]];
    for j in [1..#cols] do vecs[j][cols[j]] := R!1; end for;
    M1 := sub<M|[M!v : v in vecs]>;
    M1 := quo<M1|>; // temp fix for minimisation!
    return M1;    
end function;

intrinsic Module(S::ShfCoh) -> ModMPol
{ Returns the defining module of S }
    return S`M;
end intrinsic;

intrinsic Scheme(S::ShfCoh) -> Sch
{ Returns the scheme on which sheaf S is supported }
    return S`X;
end intrinsic;

intrinsic FullModule(S::ShfCoh) -> ModMPol
{ Returns the maximal (separated) module of S }
    if not assigned S`Mfull then
	SaturateSheaf(~S);
    end if;
    return S`Mfull;
end intrinsic;

intrinsic GlobalSectionSubmodule(S::ShfCoh) -> ModMPol
{ Returns the submodule of the maximal module of S generated in degrees
  >= 0 }
    if not assigned S`M0 then
      if not assigned S`Mfull then
	S`Mfull := ModuleSaturation(S`M);
      end if;
	S`M0 := TruncateToWeights(S`Mfull,0);
    end if;
    return S`M0;
end intrinsic;

intrinsic SaturateSheaf(~S::ShfCoh)
{ Compute the maximal graded module representing S }
    if assigned S`Mfull then return; end if;
    S`Mfull := ModuleSaturation(S`M);
end intrinsic;

///////////////// Some sheaf hom intrinsics /////////////////////////////

intrinsic Domain(f::ShfHom) -> ShfCoh
{ Domain of sheaf homomorphism }
    return f`dom;
end intrinsic;

intrinsic Codomain(f::ShfHom) -> ShfCoh
{ Codomain of sheaf homomorphism }
    return f`cod;
end intrinsic;

intrinsic Degree(f::ShfHom) -> RngIntElt
{ Degree of sheaf homomorphism }
    return f`deg;
end intrinsic;

intrinsic ModuleHomomorphism(f::ShfHom) -> ModMPolHom
{ The underlying module homomorphism of sheaf homomorphism }
    return f`hm;
end intrinsic;

intrinsic SheafHomomorphism(S::ShfCoh,T::ShfCoh,h::ModMPolHom) -> ShfHom
{ Returns the homomorphism from S to T given by h, which is a module
  homomorphism between underlying modules (defining, maximal or global sections) }

    M1 := Domain(h);
    r1 := -1;
    if assigned S`Mfull and (M1 eq S`Mfull) then
	r1 := 1;
    elif S`M eq M1 then
	r1 := 0;
    elif assigned S`M0 and (M1 eq S`M0) then
	r1 := 2;
    end if;
    require r1 ge 0:
	"Domain of argument 3 must be the defining, maximal or global section module of argument 1";

    M1 := Codomain(h);
    r2 := -1;
    if assigned T`Mfull and IsIdentical(M1,T`Mfull) then
	r2 := 1;
    elif IsIdentical(T`M,M1) then
	r2 := 0;
    elif assigned T`M0 and IsIdentical(M1,T`M0) then
	r2 := 2;
    end if;
    require r2 ge 0:
	"Codomain of argument 3 must be the defining, maximal or global section module of argument 2";

    f := New(ShfHom);
    f`dom := S; f`cod := T;
    f`r1 := r1; f`r2 := r2;
    f`deg := Degree(h);
    f`hm := h;
    return f;
       
end intrinsic;

intrinsic Expand(hms::SeqEnum[ShfHom]) -> ShfHom
{ Expands a sequence of coherent sheaf homomorphisms into a single sheaf
  homomorphism }

    require #hms gt 0: "Argument should be non-empty";
    if #hms eq 1 then return hms[1]; end if;

    /*require &+[(hms[i+1])`dom eq (hms[i])`cod : i in [1..#hms-1]]:
	"Domain of (i+1)st map must equal the codomain of the ith";*/

    require &+[Domain((hms[i+1])`hm) cmpeq Codomain((hms[i])`hm) : i in [1..#hms-1]]:
	"Domain module of (i+1)st map must equal the codomain module of the ith";

    ehm := &*[h`hm : h in hms];
    f := New(ShfHom);
    f`dom := hms[1]`dom; f`cod := hms[#hms]`cod;
    f`r1 :=  hms[1]`r1; f`r2 := hms[#hms]`r2;
    f`deg := &+[h`deg : h in hms];
    f`hm := ehm;
    return f;
 
end intrinsic;

intrinsic Image(f::ShfHom) -> ShfCoh, ShfHom, ShfHom
{ Image of a sheaf homomorphism with the restriction of the map to the image and the 
  inclusion map of the image into the codomain}

    d := f`deg;
    mp := f`hm;
    if d eq 0 then
	cod := f`cod;
    else
	cod := Twist(f`cod,d);
	mp := Homomorphism(f`dom,cod,Matrix(mp) : Check := false);		
    end if;
    M := Image(mp);

    SI := New(ShfCoh);
    SI`M := M; SI`X := cod`X; SI`Isupp := cod`Isupp;

    fres := New(ShfHom);
    fres`dom := f`dom; fres`cod := SI; fres`deg := 0;
    fres`r1 := f`r1; fres`r2 := 0;
    fres`hm := Homomorphism(Domain(mp),M,Matrix(mp) : Check := false);

    finc := New(ShfHom);
    finc`dom := SI; finc`cod := cod; finc`deg := 0;
    finc`r1 := 0; finc`r2 := f`r2;
    finc`hm := Morphism(M,Codomain(mp));

    return SI, fres, finc;
end intrinsic;

intrinsic Cokernel(f::ShfHom) -> ShfCoh, ShfHom
{ Cokernel of a sheaf homomorphism with the projection map of the 
  codomain onto it }

    M := Cokernel(f`hm);
    T := f`cod;

    SC := New(ShfCoh);
    SC`M := M; SC`X := T`X; SC`Isupp := T`Isupp;

    fquo := New(ShfHom);
    fquo`dom := T; fquo`cod := SC; fquo`deg := 0;
    fquo`r1 := f`r2; fquo`r2 := 0;
    fquo`hm := Morphism(Codomain(f`hm),M);

    return SC, fquo;
end intrinsic;

intrinsic Kernel(f::ShfHom) -> ShfCoh, ShfHom
{ Kernel of a sheaf homomorphism with the inclusion map }

    M := Kernel(f`hm);
    S := f`dom;
    SK := New(ShfCoh);
    SK`M := M; SK`X := S`X; SK`Isupp := S`Isupp;
    finc := New(ShfHom);
    finc`dom := SK; finc`cod := S; finc`deg := 0;
    finc`r1 := f`r1; finc`r2 := f`r1;
    case f`r1:
      when 0:
        finc`hm := Morphism(M,S`M);
      when 1:
        finc`hm := Morphism(M,S`Mfull);
	SK`Mfull := SK`M;
      when 2:
        finc`hm := Morphism(M,S`M0);
	SK`M0 := SK`M;
    end case;
    return SK, finc;
end intrinsic;

//////////////// Divisor maps, RR spaces, divisor to sheaf /////////////////

intrinsic DivisorMap(S::ShfCoh : graphmap := false) -> Map,Sch
{ Returns the (rational) divisor map associated to the invertible sheaf on X
  given by S and the image of this map. The map returned is usually a scheme
  graph map but may also be a traditional MapSch. If the graphmap parameter
  is set to true, a MapSchGrph is definitely returned.}
    if (assigned S`div_map) and ((not graphmap) or (
		ISA(Type(S`div_map),MapSchGrph))) then
	return S`div_map,Image(S`div_map);
    end if;
    if not assigned S`M0 then
      if not assigned S`Mfull then
	S`Mfull := ModuleSaturation(S`M);
      end if;
      S`M0 := TruncateToWeights(S`Mfull,0);
    end if;
    M0 := GlobalSecSubmod(S`M0);
    rels := RelationMatrix(M0);
    gr_map,mp_im := ImageFromMat(rels,S`Isupp,S`X,0);
    S`div_map := gr_map;
    return gr_map,mp_im;
end intrinsic;

intrinsic IntersectionPairing(S1::ShfCoh,S2::ShfCoh) -> RngIntElt
{ S1 and S2 are invertible sheaves representing Cartier Divisors D1
  and D2 on the same surface X. Returns the intersection number D1.D2 }

    require S1`X cmpeq S2`X:
	"S1 and S2 must be sheaves on the same projective surface";
    require Dimension(S1`X) eq 2:
	"S1 and S2 must be (invertible) sheaves on a surface";
    p_a := ArithmeticGenus(S1`X);
    chi_D1 := Coefficient(MyHilbertPolynomial(S1`M),0);
    chi_D2 := Coefficient(MyHilbertPolynomial(S2`M),0);
    chi_D1_pl_D2 := Coefficient(MyHilbertPolynomial(TensorProduct(S1`M,S2`M)),0);
    return 1 + chi_D1_pl_D2 + p_a - chi_D1 - chi_D2;
end intrinsic;

intrinsic TensorProduct(S1::ShfCoh,S2::ShfCoh : Maximize := false) -> ShfCoh
{ Computes the tensor product of two sheaves on the same scheme. If Maximize
  (default false) is true, the maximal module of the result is used. }

    require S1`X cmpeq S2`X:
	"S1 and S2 must be sheaves on the same projective scheme";

    Mt := TensorProduct(S1`M,S2`M : Minimize := true);
    if Maximize then
	Mt := ModuleSaturation(Mt);
    end if;
    St := New(ShfCoh);
    St`M := Mt; St`X := S1`X; St`Isupp := S1`Isupp;
    if Maximize then
	St`Mfull := Mt;
    end if;
    return St;

end intrinsic;

intrinsic TensorPower(S::ShfCoh,n::RngIntElt : Maximize := true) -> ShfCoh
{ Computes the nth tensor power of S for n a positive or negaitive integer.
  If Maximize (default true) is true, the maximal module of the result is
  used. }

    if n eq 0 then
	return StructureSheaf(S`X);
    end if;
    if n lt 0 then
	S := Dual(S);
	n := -n;
    end if;
    if n eq 1 then return S; end if;
    // do by binary expansion
    bits := Intseq(n,2);
    Prune(~bits); Reverse(~bits);
    T := S;
    for b in bits do
	T := TensorProduct(T,T: Maximize := Maximize);
	if b eq 1 then
	    T := TensorProduct(S,T: Maximize := Maximize);
	end if;
    end for;
    return T;
    
end intrinsic;

intrinsic DirectSum(S1::ShfCoh,S2::ShfCoh) -> ShfCoh
{ The direct sum of sheaves S1 and S2 }

    require S1`X cmpeq S2`X:
	"S1 and S2 must be sheaves on the same projective scheme";

    Ms := DirectSum(S1`M,S2`M);
    Ss := New(ShfCoh);
    Ss`M := Ms; Ss`X := S1`X; Ss`Isupp := S1`Isupp;
    if assigned S1`Mfull and assigned S2`Mfull then
	Ss`Mfull := DirectSum(S1`Mfull,S2`Mfull);
    end if;
    if assigned S1`M0 and assigned S2`M0 then
	Ss`M0 := DirectSum(S1`M0,S2`M0);
    end if;
    if assigned S1`loc_free_rk and assigned S2`loc_free_rk then
	if (S1`loc_free_rk eq -1) or (S2`loc_free_rk eq -1) then
	   Ss`loc_free_rk := -1;
	else
	   Ss`loc_free_rk := S1`loc_free_rk + S2`loc_free_rk;
	end if;
    end if;
    if assigned S1`is_arith_CM and assigned S2`is_arith_CM then
	Ss`is_arith_CM := (S1`is_arith_CM and S2`is_arith_CM);
    end if;

    return Ss;

end intrinsic;

intrinsic DivisorToSheaf(X::Sch,I::RngMPol: GetMax := true) -> ShfCoh
{ Returns the invertible sheaf <-> the (locally principal) effective divisor on X
  defined by ideal I. If GetMax is true (the default), the module computed is
  the maximal separated one, the associated divisor map is computed and stored and
  a basis for the Riemann-Roch space is computed and stored at the same time in a
  slightly more efficient way than for the direct sheaf computation.}

    R := CoordinateRing(Ambient(X));
    Saturate(~X);
    require Generic(I) eq R:
	"I doesn't lie in the coordinate ring of X";
    Saturate(~X);
    IX := Ideal(X);
    ID := Saturation(I + IX);
    
    // IDEA: let r be the smallest s.t. ID_r != IX_r.
    //  Let Fr in ID_r\IX_r and IE=(<Fr>+IX:ID). Then
    //  IE is the ideal defining an effective divisor of X with D+E=rH where
    //  H is the hyperplane section and L(D)=L(rH-E) which is represented by
    //  the module (IE/IX)(r).
    //  Note also that (IE/IX)(r) will be saturated in degrees >= 0 if
    //  R_i = (R/I)_i [ith graded pieces] for i >= r

    dX := Degree(HilbertPolynomial(IX)); dD := Degree(HilbertPolynomial(ID));
    require dX eq dD+1:
	"I doesn't define a codimnension 1 subscheme of X";
    hD := HilbertSeries(ID);
    hX := HilbertSeries(IX);
    hXD := hX-hD;
    r := Valuation(Numerator(hXD));

    // find an Fr
    BX := GroebnerBasis(IX); 
    Reverse(~BX); 
    if IsEmpty(BX) then
      BX := [Generic(IX)| 0];
    end if;
    BD := GroebnerBasis(ID);
    Reverse(~BD);
      // assumed here that R has a degree ordering
    i := 1; while LeadingTotalDegree(BD[i]) lt r do i +:=1; end while;
    if LeadingTotalDegree(BX[#BX]) ge r then
      j := 1; while LeadingTotalDegree(BX[j]) lt r do j +:=1; end while;
      while (j le #BX) and (BD[i] eq BX[j]) do 
	j +:=1; i +:=1;
      end while;
    end if;
    Fr := BD[i];
    // NB : really need to check that Fr not an IX zero-divisor here.
    //  If IX is equidimensional then STP that Dim(<Fr,IX>)=Dim(IX)+1

    r1 := r;
    if GetMax then
	n := Rank(R);
	OXres := MinimalFreeResolution(QuotientModule(IX));
	if #Terms(OXres) ge n+2 then
	    assert  #Terms(OXres) eq n+2; //as IX is saturated
	    h1 := Term(OXres,n-1);
	    // Ext^(n-1)(R/I,R) is a quotient of the dual of h1.
	    // This is dual to sum_r H^1(P^(n-1),I(r)) with the
	    // r graded piece <-> the (-n-r)th graded piece of
	    // the Ext module. We want the max r >= 0 s.t.
	    // this rth graded piece is non-zero which is the
	    // max r s.t. R_r -> (R/I)_r ISN't onto (if r exists)
	    r1 := Max(ColumnWeights(h1))-n+1;
	    r1 := Max(r,r1);	    
	end if;
    end if;
    if r1 gt r then
	//as IX saturated, x^(r1-r)Fr not in IX for some variable x
	i := 1; while (R.i)^(r1-r)*Fr in IX do i +:=1; end while;
	Fr := Fr * (R.i)^(r1-r);
    end if;

    // Get IE
    IXF := Saturation(IX+ideal<R|Fr>);
    IE := ColonIdeal(IXF,ID); // IE is automatically saturated
    
    // Get (IE/IX)(r1)
    M0 := QuotientModule(IX);
    M0 := Twist(M0,r1);
    M := sub<M0|[M0![b] : b in Basis(IE)]>;
    M := quo<M|>; // temp fix for minimisation!

    S := New(ShfCoh);
    S`M := M; S`X := X; S`Isupp := IX; S`Iann := IX;
    if GetMax then
	S`Mfull := M;
	//get basis for divisor map
	B := QuotientIdealBasis(IE,IX,r1);
	S`rr_space := <B,Fr>;
	S`div_map := map<X->ProjectiveSpace(BaseRing(X),#B-1)|B>;
	M0 := sub<M0|[M0![b] : b in B]>;
	M0 := quo<M0|>; // temp fix for minimisation!
	S`M0 := M0;		
    end if;
 
    return S;

end intrinsic;

intrinsic RiemannRochBasis(X::Sch,I::RngMPol) -> SeqEnum, RngMPolElt, ShfCoh
{ Returns a basis for the Riemann-Roch space of the (locally principal) effective divisor
  D on variety X defined by ideal I. Returned as a sequence [F1,..,Fn] of numerators
  and a denominator G such that rational functions Fi/G on X give a basis for L(D).
  An invertible sheaf representing the divisor class of D is also returned.}

    S := DivisorToSheaf(X,I : GetMax := true);
    rr_sp := S`rr_space;
    return rr_sp[1], rr_sp[2], S;

end intrinsic;

/////////// Some Attribute Intrinsics ///////////////////////////////

  ///// Locally free test functions /////

function is_loc_free_generic(S : norm_data := 0)

    // Test for whether S is locally free generically
    // on its scheme X, assumed equidimensional and CM. More specifically,
    // test is a necessary condition for loc freeness on X, and
    // if the test is passed, S is locally free outside of the ramification
    // locus of X->P^m corresponding to the noether normalisation of X
    // (norm data should contain this specific n. n. info if a specific
    //  n. n. is to be used). If result is true, also returns the rank
    //  of local freeness.


    // IDEA: First note that X CM and equi => X is faithfully flat
    // over Proj(R0) where R0 is a (linear) Noether normalisation for
    // the coordinate ring R/I of X. Then S is loc free iff M is flat
    // over R/I => M is flat over R0 (away from the redundant primes)
    // iff S is locally free over Proj(R0). The converse is true away
    // from the ramification locus of X->Proj(R0). So we can work with the
    // "projection of M", Mprj - a graded module over polynomial ring R0.
    //
    // Then use Serre's cohomological criterion that, if R0=k[x1..,xm],
    // then S is locally free iff the cohomology spaces H^i(S(r))
    // vanish for r << 0 for all 0 <= i < m-1. By duality, this
    // equates to Ext^i(Mprj,R0) a FINITE LENGTH R0 module for
    // 0 < i <= m-1. We also have the necessary condition
    // sat(Iann) = Isupp.

    if not assigned S`Iann then
	S`Iann := Saturation(Annihilator(S`M));
    end if;

    if not S`Iann subset S`Isupp then
	return false,_;
    end if;

    if not assigned S`Mprj then
      if assigned S`Mfull then
	Mprj,xmats,xmap := GenModuleProject(S`Mfull : norm_data := norm_data);
	S`Mprj := Mprj; S`xmats := xmats; S`xmap := xmap;
	S`prj_is_full := true;
      else
	Mprj,xmats,xmap := GenModuleProject(S`M : norm_data := norm_data);
	S`Mprj := Mprj; S`xmats := xmats; S`xmap := xmap;
	S`prj_is_full := false; 
      end if;
    end if;

    // Now, rather than computing the full Exts, it is more efficient
    // to compute the Hilbert polys of the appropriate im(fi) and 
    // ker(f_(i+1)), fi the maps of the dual complex of the min free res
    // of Mprj, and check that they are the same [<=> quot mod is
    // fin length]. Using additivity of Hilb polys over SESs, and
    // the trivial nature of the Hilbert poly for a graded free module,
    // we reduce to just computing the hilbert polys of Fi/im(fi), which
    // is fairly fast, and checking an additive equality.
    Mprj := S`Mprj;
    R0 := BaseRing(Mprj);
    n := Rank(R0);
    res := MinimalFreeResolution(Mprj);
    r := #Terms(res)-3;
    d := &+[((-1)^i)*Rank(Term(res,i)) : i in [0..r]];
    // d = Rank of Mprj as an R0 module
    // If the dual of min_res is F0 -> F1 -> F2 -> .. -> Fr -> 0
    // with fi:F_(i-1)->Fi, then have to check that
    // HilbPoly(F_(i+1)) = HilbPoly(Fi/im(fi))+HilbPoly(F_(i+1)/im(f_(i+1)))
    // for 1<=i<=n-1
    boo := true;
    hsi := RationalFunctionField(Integers())!0;
    hsi1 := hsi; hsd := hsi;
    for i in [1..Min(n,r+1)] do
	wtsi := [-w : w in ColumnWeights(Term(res,i))];
	if #wtsi gt 0 then // i <= r
	  fi := Transpose(Matrix(BoundaryMap(res,i)));
	  Fi := RModule(R0,wtsi);
	  hsi := MyHilbertSeries(quo<Fi|[Fi!r : r in RowSequence(fi)]>);
	end if;
	if (i gt 1) and (i ne r+1) then
	    hsd := hsi+hsi1-SpecialHilbertSeries(Fi);
	elif i eq r+1 then
	    hsd := hsi1;    
	end if;
	hsi1 := hsi;	
	boo := (den eq (Parent(den).1)^Degree(den)) where den is Denominator(hsd);
	if not boo then break; end if;
    end for;

    if not boo then
	return false,_;
    else
	// rank of R/I as an R0 module is just Degree(X)
	dX := Degree(S`X);
	boo,rk := IsDivisibleBy(d,dX);
	assert boo;
	S`loc_free_rk := rk;
	return true,rk;		
    end if;

end function;

function free_test_dim_zero(S,d)

    X := S`X;
    deg := Degree(X);
    // quick test
    if Integers()!Evaluate(HilbertPolynomial(S`M),0) ne
	d*deg then
	  return false;
    end if;
    if Degree(X) eq 1 then
	cmps := [X];
    else
	cmps := PrimaryComponents(X);
    end if;
    
    for Y in cmps do
	SY := (#cmps eq 1) select S else Restriction(S,Y : Check := false);
	if (#cmps gt 1) and 
	  (Integers()!Evaluate(HilbertPolynomial(SY`M),0) ne
		d*Degree(Y)) then
	  return false;
	end if;
	if not Saturation(Annihilator(SY`M)) subset SY`Isupp then
	  return false;
	end if;
    end for;
    return true;

end function;

function inductive_free_test(S,S0,nod,d)

    dX := Dimension(S`X);
    if dX eq 0 then //need to do this properly
	return free_test_dim_zero(S,d);
    end if;
    R := BaseRing(S`M);
    // first need to check whether nod`F
    // is a zero divisor on S
    if TotalDegree(nod`F) gt 0 then
	M := (assigned S0`Mfull) select S0`Mfull else S0`M;
	hm := Homomorphism(M,M,ScalarMatrix(R,#ColumnWeights(M),nod`F) : Check := false);
	K := Kernel(hm);
	if (not IsZero(K)) and IsProper(Saturation(Annihilator(K))) then
	  return false;
	end if;
    end if;
    // next do locally free test on the 'generic' part
    boo,d1 := is_loc_free_generic(S : norm_data := 
	<[(nod`xmap)(R.i) : i in [n-dX..n]],nod`xmapi,nod`xmap>) where
	n is Rank(R) where R is BaseRing(S`M);
    if not boo or (d ne d1) then return false; end if;
    // finally, do loc free test on the non-etale part
    lst := nod`lower_strat;
    for n in lst do
	boo := inductive_free_test(Restriction(S,n`X : Check := false),S,n,d);
	if not boo then return false; end if;
    end for;
    return true;
                  
end function;

function loc_free_by_fitting(M,I,d)
// M is a reduced module over polynomial ring R annihilated by 
// (saturated) homog ideal I < R.
// Returns whether M is locally free of rank d as an (R/I)
// module except possibly at the maximal homog ideal of R/I

    // minimise relations for more efficient Fitting comp
    cwts := ColumnWeights(M);
    R := BaseRing(M);
    rels := Relations(M);
    F := Module(R,cwts);
    relM := sub<F|[F!Eltseq(r) : r in rels]>;
    B := MinimalBasis(relM);
    if #B lt #rels then
	M := quo<F|[F!Eltseq(b) : b in B]> where
		F is RModule(R,cwts);
    end if;
    delete B,relM;

    Id := FittingIdeal(M,d);
    boo := (R!1 in Saturation(Id)); //sat(Id)=R
    delete Id;
    if boo then
	Idm1 := FittingIdeal(M,d-1);
	boo := (Idm1 subset I); //sat(Idm1) <= I 
    end if;
    return boo;

end function;

intrinsic IsLocallyFree(S::ShfCoh : UseFitting := true) -> BoolElt, RngIntElt
{ Returns whether S is a locally free sheaf of constant rank on its scheme X
  and, if so, its rank.
  If parameter UseFitting is true (the default), uses Fitting ideals.
  Otherwise, uses the etale stratification method described in the handbook.
  Assumed that X is equidimensional, connected and (locally)
  Cohen-Macualay for the stratification method. }

    if assigned S`loc_free_rk then
	if S`loc_free_rk eq -1 then return false,_;
	else return true,S`loc_free_rk; end if;
    end if;

    //special case: dimension 0
    if Dimension(S`X) eq 0 then
	return true,Integers()!Evaluate(HilbertPolynomial(S`M),0);
    end if;    

    if not assigned S`Iann then
	S`Iann := Saturation(Annihilator(S`M));
    end if;

    if not S`Iann subset S`Isupp then
	S`loc_free_rk := -1;
	return false,_;
    end if;

    // find the possible locally free rank d
    hS := MyHilbertPolynomial(S`M); hX := HilbertPolynomial(S`Isupp);
    assert Degree(hS) eq Degree(hX);
    d := LeadingCoefficient(hS)/LeadingCoefficient(hX);
    if not IsIntegral(d) then
	S`loc_free_rk := -1;
	return false,_;
    end if;
    d := Integers()!d;
    assert d gt 0;

    if UseFitting then
	M := (assigned S`Mfull) select S`Mfull else S`M;
	boo := loc_free_by_fitting(M,S`Iann,d);
    else
	nod := EtaleStratification(S`X);
	boo := inductive_free_test(S,S,nod,d);
    end if;

    if not boo then
	S`loc_free_rk := -1;
	return false,_;
    else
	S`loc_free_rk := d;
	return true,d;		
    end if;

end intrinsic;

  ///////////////////////////////////////

intrinsic IsArithmeticallyCohenMacaulay(S::ShfCoh) -> BoolElt
{ Returns whether the maximal separated module representing S
  is a CohenMacaulay module of maximal dimension over the coordinate
  ring of its scheme X (which is assumed equidimensional).}

    if not assigned S`is_arith_CM then
	if not assigned S`Mfull then
	    S`Mfull := ModuleSaturation(S`M);
	end if;
	if (assigned S`Mprj) and (S`prj_is_full eq true) then
	    // cheap comp using Mprj : criterion is that it is
	    // free over R0
	    S`is_arith_CM := (#Relations(S`Mprj) eq 0);
	else
	    n := Rank(BaseRing(S`M));
	    res := MinimalFreeResolution(S`Mfull);
    	    dep := n+3-#Terms(res);  //depth of Mfull at max ideal
	    S`is_arith_CM := (dep eq Dimension(S`X)+1);
	end if;
    end if;	
    return S`is_arith_CM ;
   
end intrinsic;

intrinsic CohomologyDimension(S::ShfCoh,r::RngIntElt,n::RngIntElt) -> RngIntElt
{ The dimension of the cohomology group H^r(X,S(n)) over the base field, where S(n)
  is the nth Serre twist of coherent sheaf S }

    M := S`M;
    if assigned S`Mfull /*and Rank(S`Mfull) le Rank(M)*/ then
	M := S`Mfull;
    end if;
    return CohomologyDimension(M,r,n);

end intrinsic;

intrinsic DimensionOfGlobalSections(S::ShfCoh) -> RngIntElt
{ The dimension of the space of global section of $S$, H^0(S), over the base field.
  (Usually faster) alternative to CohomologyDimension(S,0,0). }

    return h0(S);

end intrinsic;

function hom_elt_to_hom(m,hm,S,T)
    M :=  Parent(m);
    if m ne 0 then
	wts := ColumnWeights(M);
	es := Eltseq(m);
	boo := &and[IsHomogeneous(e) : e in es | e ne 0];
	if boo then
	  ds := [wts[i]+LeadingTotalDegree(es[i]) : i in [1..#es] | es[i] ne 0];
	  d := ds[1];
	  boo := &and[e eq d : e in ds];
	end if;
    else
	boo := true; d := 0;
    end if;
    error if not boo,
	"Argument of map should be a homogeneous element in the module of the domain sheaf";

    shm := New(ShfHom);
    shm`dom := S; shm`cod := T; shm`r1 := 1; shm`r2 := 1;
    shm`hm := hm(m);
    shm`deg := d;
    return shm;
end function;

intrinsic Dual(S::ShfCoh) -> ShfCoh
{ Returns the dual sheaf of S, Hom(S,O_X) where O_X is the structure sheaf
  of the scheme of S }
    SD := SheafHoms(S,StructureSheaf(S`X));
    return SD;
end intrinsic;

intrinsic SheafHoms(S::ShfCoh,T::ShfCoh) -> ShfCoh, Map
{ Returns the sheaf Hom(S,T) and a map on the underlying module of
  Hom(S,T) that takes homogeneous elements to the actual homomorphism they 
  represent }

    require S`X cmpeq T`X:
      "Sheaves musts be defined on the same base scheme";

    if not assigned S`Mfull then
	S`Mfull := ModuleSaturation(S`M);
    end if;
    if not assigned T`Mfull then
	T`Mfull := ModuleSaturation(T`M);
    end if;

    Mhms,hms_mp := Hom(S`Mfull,T`Mfull);
    Iann := Annihilator(Mhms);
    Shms := New(ShfCoh);
    Shms`M := Mhms; Shms`X := S`X; Shms`Isupp := S`Isupp; 
    Shms`Iann := Iann; Shms`Mfull := Mhms;

    // NB: Must also return map: requires elements!
    return Shms, map<Mhms -> PowerStructure(ShfHom) | x :-> 
			hom_elt_to_hom(x,hms_mp,S,T)>;

end intrinsic;

function sort_with_perm(seq)
    n := #seq;
    seq1 := Sort(seq); perm := [];
    st1 := Setseq(Seqset(seq1));
    Sort(~st1);
    for s in st1 do
	perm cat:=  [i : i in [1..n] |seq[i] eq s];
    end for;
    //if perm eq [1..n] then perm := []; end if;
    return seq1,perm;   
end function;

function minimal_relation_matrix(M)
    rels := RelationMatrix(M);
    colwts := ColumnWeights(M);
    F := Module(BaseRing(M),colwts);
    S := sub<F|[F!r : r in RowSequence(rels)]>;
    B := MinimalBasis(S);
    wts := [Degree(b) : b in B];
    wts1,perm := sort_with_perm(wts);
    mat := Matrix(BaseRing(M),[Eltseq(B[i]) : i in perm]);
    return mat,wts1;	
end function;

function my_rand(K)
    case Type(K):
      when FldFin: return Random(K); 
      when FldRat: return Rationals()!Random(-3,3);
    end case;
end function;

function det_pol(Ms,P)
    r := Rank(P); mons := [P.i : i in [1..r]];
    return Determinant(Matrix([[Polynomial([Ms[i][j,k] : i in [1..r]],mons):
	k in [1..n]] : j in [1..n]])) where n is Nrows(Ms[1]);
end function;

function non_zero_pt(F)

    //NB: Need to do this properly in case the base field
    // is of characteristic p but not finite!
    P := Parent(F);
    r := Rank(P);
    K := BaseRing(P);
    degs := [Degree(F,i) : i in [1..r]];
    d := Min(degs);
    i := Index(degs,d);
 
    if (Type(K) eq FldFin) and (#K le d) then
	// do complete point search
	for v in  CartesianPower(K,r) do
	    if Evaluate(F,v) ne K!0 then
		return true, [v[j] : j in [1..r]];
	    end if;
	end for;
	return false,_;
    end if;

    if r gt 1 then
      P1 := PolynomialRing(K,r-1);
      hm := hom<P->P1|[P1.j : j in [1..i-1]] cat [P1!0] cat 
	[P1.j : j in [i..r-1]]>;
      i0 := 0;
      cs := [hm(c) : c in Coefficients(F,i)];
      for j in [1..d+1] do
        if cs[j] ne P1!0 then
	  boo,v := non_zero_pt(cs[j]);
	  if boo then i0 := j; break; end if;
        end if;
      end for;   
    
      if i0 eq 0 then return false,_;
      elif i0 eq 1 then
	Insert(~v,i,K!0);
	return true,v;
      elif i0 eq d+1 then
	Insert(~v,i,K!1);
	return true,v;
      end if;
      pol := PolynomialRing(K)![Evaluate(cs[j],v) : j in [i0..d+1]];
    else
      pol := UnivariatePolynomial(F);
      if Coefficient(pol,0) ne K!0 then
	return true,[K!0];
      elif #Support(pol) eq 1 then
	return true,[K!1];
      end if;
    end if;

    if Type(K) eq FldFin then
	while true do
	    t := Random(K);
	    if (t ne K!0) and (Evaluate(pol,t) ne K!0) then break; end if;
	end while;
    else
	for j in [1..d] do
	  if Evaluate(pol,K!j) ne K!0 then
	    t := K!j; break;
	  elif Evaluate(pol,-K!j) ne K!0 then
	    t := -K!j; break;
	  end if;
	end for;
    end if;
    if r eq 1 then return true,[t]; end if;        
    Insert(~v,i,t);
    return true,v;	  
end function;

/*
function non_singular_mat_indep(Ms)
// As below only Ms are linearly independent n x n matrices

    // Strategy: work recursively. Choose M in Ms of maximal
    // rank, Smith diagonalise it, and then look for a combination
    // L of the rest whose appropriate lower diagonal block is
    // non-singular. Then can take tM+L for some t.
    if (#Ms eq 1) then
	if IsSingular(Ms[1]) then
	    return false,_;
	else
	    return true,[BaseRing(Ms[1])!1];
	end if;
    end if;

    n := Nrows(Ms[1]); K := BaseRing(Ms[1]);
    rks := [];
    for M in Ms do
	Append(~rks,Rank(M));
	if rks[#rks] eq n then break; end if;
    end for;
    if rks[#rks] eq n then
	return true,[K|0 : j in [1..#rks-1]] cat [K!1] cat
		[K|0 : j in [#rks+1..#Ms];
    end if;

    rm := Max(rks); i := Index(rks,rm);
    if (Type(K) eq FldFin) and (#K le rm) then
	// det(tM+L) may be 0 for all t: use the
	// complete determinant method
	return non_singular_mat_indep_det(Ms);
    end if;

    _,P,Q := SmithForm(Ms[i]);
    Ms1 := [P*Ms[j]*Q : j in [1..#Ms] | j ne i];
    boo,v := non_singular_mat(
	[ Submatrix(m,rk+1,rk+1,n-rk,n-rk) : m in Ms1]);
    if not boo return false,_; end if;
    det := Determinant(
	DiagonalMatrix([R.1 : j in [1..rk]] cat [R!0: j in [rk+1..n]]) +
	ChangeRing(&+[v[j]*Ms1[j] : j in [1..#v] | v[j] ne 0],R) )
	  where R is PolynomialRing(K);
    
    // now just specialise t so that det is non-zero
    // NB! for infinite fields in char p, have to do
    //  something different in general!
    t := K!0;
    if Coefficient(det,0) eq K!0 then
      if Type(K) eq FldFin then
	while true do
	    t := Random(K);
	    if Evaluate(det,t) ne K!0 then break; end if;
	end while;
      else
	for j in [1..rk] do
	  if Evaluate(det,K!j) ne K!0 then
	    t := K!j; break;
	  elif Evaluate(det,-K!j) ne K!0 then
	    t := -K!j; break;
	  end if;
	end for;
      end if;
    end if;
    Insert(~v,i,t);
    return true,v;
end function;
*/

function non_singular_mat(Ms,bks)
// Given a sequence of n x n matrices over field k, determine
// whether there is a k-linear combination that is non-singular.

    if #Ms eq 0 then return false,_; end if;
    // First find a basis B for the space generated by Ms
    K := BaseRing(Ms[1]);
    n := Nrows(Ms[1]);
    vs := VectorSpace(K,n^2);
    Mvs := [Eltseq(M) : M in Ms];
    W := sub<vs|[vs!v : v in Mvs]>;
    coords := [Coordinates(W,W!m) : m in Mvs];
    flt := Transpose(Matrix(coords));
    ech := EchelonForm(flt);
    b_inds := [Min(Support(r)) : r in Rows(ech) | not IsZero(r)];
    if #b_inds eq 0 then return false,_; end if;
    B := [Ms[i]: i in b_inds];
    assert #B le n^2;
    delete ech,flt,coords,W,Mvs,vs;
    
    /*boo,v := non_singular_mat_indep(B);
    if not boo then
	return false,_;
    else
	v1 := [(i eq 0) select K!0 else v[i] where i is Index(b_inds,j):
		j in [1..#Ms]];
	return true,v1;
    end if;*/
    if (#B eq 1) then
	if IsSingular(B[1]) then
	    return false,_;
	else
	    return true,[K!0 : i in [1..b_inds[1]-1]] cat [K!1] cat
		[K!0 : i in [b_inds[1]+1..#Ms]];
	end if;
    end if;
    
    v := [K!0 : j in [1..#Ms]];
    done := false;

    // over Q and fin flds, try some random linear combinations
    if (K cmpeq Rationals()) or (Type(K) cmpeq FldFin) then
      for j in [1..5] do
	v1 := [my_rand(K) : k in [1..#B]]; r := 1;
	for m in bks do
	  det := Determinant(&+[v1[k]*Submatrix(B[k],r,r,m,m): k in [1..#B]]);
	  if det eq K!0 then break; end if;
	  r +:= m;
	end for;
	if det ne K!0 then 
	  done := true; break;
	end if;	  
      end for;
    end if;

    if not done then
      P := PolynomialRing(K,#B,"grevlex");
      r := 1;
      F := P!1;
      for m in bks do
	F *:= det_pol([Submatrix(M,r,r,m,m): M in B],P);
	r +:= m;
      end for;

      if F eq P!0 then 
	return false,_;
      else 
	boo,v1 := non_zero_pt(F);
	if not boo then return false,_; end if;
      end if;
    end if;

    for j in [1..#B] do
	v[b_inds[j]] := v1[j];
    end for;
    return true,v;
   
end function;   

/*
intrinsic IsIsomorphic(S::ShfCoh,T::ShfCoh) -> BoolElt, Rec, RngIntElt
{ Returns whether sheaves S and T are isomorphic }

    // Idea: if M and N are modules representing S,T then
    //  look for an IM between M_{>= r} and N_{>=r} where
    //  r >= max{Reg(M),Reg(N)}. In this case, the rth
    //  Veronese modules of M and N are generated in degree
    //  r and only have linear relations so are completely
    //  determined by their rth and (r+1)th graded parts
    //  and the multiplication by xi linear maps from 
    //  M(N)_r -> M(N)_(r+1). This then gives a set of
    //  linear equations over the base field to determine 
    //  whether M_{>= r} and N_{>=r} are isomorphic.
    //
    //  On the other hand, this can involve rather large
    //  dimensional spaces. There is in essence, some
    //  redundancy involved compared to looking for maps
    //  between minimal presentations of maximal modules
    //  of S and T. There, the (often non-trivial) weight
    //  structure will force zeros and this immediate
    //  info is lost in passing to the Veroneses. However,
    //  in this case the matrix equations involving
    //  polynomials of different degrees are more complicated
    //  to deal with directly [if we want to avoid a
    //  completely generic Groebner Hom(M,N) comp].
    

    // If an explicit IM is needed then have to extend
    
    // First do simple Hilbert polynomial check.
    if MyHilbertPolynomial(S`M) ne MyHilbertPolynomial(T`M) then
	return false,_;
    end if;

    
end intrinsic;
*/


function find_isomorphism(S,T,with_twist)
    //Do more sophisticated version later!
    
    // First do simple Hilbert polynomial check (up to twist).
    HS := MyHilbertPolynomial(S`M);
    HT := MyHilbertPolynomial(T`M);
    if HS ne HT then
      if not with_twist then return false,_,_; end if;
      if (Degree(HS) eq Degree(HT)) and (LeadingCoefficient(HS) eq
		LeadingCoefficient(HT)) then
	r := (Coefficient(HT,d-1)-Coefficient(HS,d-1))/
	      (d*LeadingCoefficient(HS)) where d is Degree(HS);
	if (r notin Integers()) or (Evaluate(HS,Parent(HS).1+r) ne HT)
		then return false,_,_;
	end if;
      else
	return false,_,_;
      end if;
    end if;

    // Next check that Betti numbers are the same up to shift.
    //  the shift will give the 'twist' in an isomorphism
    if not assigned S`Mfull then
	S`Mfull := ModuleSaturation(S`M);
    end if;
    if not assigned T`Mfull then
	T`Mfull := ModuleSaturation(T`M);
    end if;    
    SM := S`Mfull; TM := T`Mfull;
    col1,p1 := sort_with_perm(ColumnWeights(SM));
    col2,p2 := sort_with_perm(ColumnWeights(TM));
    if #col1 ne #col2 then return false,_,_; end if;
    d := col2[1]-col1[1];
    if (not with_twist) and (d ne 0) then return false,_,_; end if;
    if [c+d: c in col1] ne col2 then return false,_,_; end if;
    Stab,dS := BettiTable(SM);
    Ttab,dT := BettiTable(TM);
    Stab := Matrix(Integers(),Stab);
    Ttab := Matrix(Integers(),Stab);
    if not (Stab cmpeq Ttab) then
	return false,_,_;
    end if;
    assert d eq dT-dS;

    /*
    // Get minimal relation matrices, permuting columns of SM and TM
    //  so they are in increasing weight order
    relS,wtS := minimal_relation_matrix(SM);
    relT,wtT := minimal_relation_matrix(TM);
    assert [w+d : w in wtS] eq wtT;
    rwts := wtS;
    */

    // For the moment, just uses generic Homs code - should
    //  do a more tuned computation for this important case.
    hms,hms_mp := Hom(SM,(d eq 0 select TM else Twist(TM,d)));
    if Rank(hms) le 0 then return false,_,_; end if;
    hmc := ColumnWeights(hms);
    assert &and[wt ge 0 : wt in hmc]; // sanity check!
    B := [hms.i : i in [1..#hmc] | hmc[i] eq 0];
    if #B eq 0 then return false,_,_; end if;
               
    // B is a basis for degree 0 maps between SM and TM(d).
    // The matrix for such a map is a block matrix with
    // the parts corresponding to the maps between columns
    // of the same weight being matrices over the base field k.
    // SM & TM(d) are isomorphic iff there is a map such that
    // these parts are all isomorphisms.
    P := BaseRing(SM); K := BaseRing(P);
    bk_wts := []; bk_ls := []; col_pairs := [];
    i := 0; wt := col1[1]; c1 := []; c2 := []; 
    for j in [1..#col1] do
	if col1[j] eq wt then
	    i +:= 1; Append(~c1,p1[j]); Append(~c2,p2[j]);
	else
	    Append(~bk_wts,wt); Append(~bk_ls,i);
	    Append(~col_pairs,[c1,c2]);
	    i := 1; wt := col1[j]; c1 := [p1[j]]; c2 := [p2[j]];
	end if;
    end for;
    Append(~bk_wts,wt); Append(~bk_ls,i);
    Append(~col_pairs,[c1,c2]);
    B0 := [];
    for b in B do
	mat := Matrix(hms_mp(b));
	//mat1 := DiagonalJoin([Submatrix(mat,c[1],c[2]) : c in col_pairs]);
	//mat1 := ChangeRing(mat1,K);
	Append(~B0,[* ChangeRing(Submatrix(mat,c[1],c[2]),K) : c in col_pairs *]);
    end for;
    // first check whether a basis element is invertible
    //  - probably true if an IM exists
    good_ind := 0;
    for i in [1..#B] do
	if &and[ not IsSingular(m) : m in B0[i]] then
	    good_ind := i; break;
	end if;
    end for;
    if good_ind ne 0 then
	f := New(ShfHom);
	f`dom := S; f`cod := T; f`r1 := 1; f`r2 := 1; f`deg := d;
	hm := hms_mp(B[good_ind]);
	f`hm := ((d eq 0) select hm else
		Homomorphism(SM,TM,Matrix(hm) : Check := false));
	return true, d, f;
    end if;
    // now check if trivially false because one block is 0 for all maps
    bad_ind := 0;
    for j in [1..#col_pairs] do
	if &and[IsZero(ms[j]) : ms in B0] then
	    bad_ind := j; break;
	end if;
    end for;
    if bad_ind gt 0 then return false,_,_; end if;           
    
    // Do general non-singular-in-subspace routine. This is very
    // inefficient right now! Can it be improved??
    djs := [];
    for ms in B0 do
        dj := ms[1];
	for j in [2..#ms] do dj := DiagonalJoin(dj,ms[j]); end for;
	Append(~djs,dj);
    end for;
    boo,seq := non_singular_mat(djs, [Nrows(m) : m in B0[1]]);
    if not boo then return false,_,_; end if;
    
    if #[s : s in seq | s ne K!0] eq 1 then
	ind := 1;
	while seq[ind] eq K!0 do ind +:= 1; end while;
	hmB := B[ind];
    else
	hmB := &+[seq[i]*B[i] : i in [1..#seq] | seq[i] ne K!0];
    end if;
    f := New(ShfHom);
    f`dom := S; f`cod := T; f`r1 := 1; f`r2 := 1; f`deg := d;
    hm := hms_mp(hmB);
    f`hm := ((d eq 0) select hm else
		Homomorphism(SM,TM,Matrix(hm) : Check := false));
    return true, d, f;

end function;

intrinsic IsIsomorphicWithTwist(S::ShfCoh,T::ShfCoh) -> BoolElt, RngIntElt, ShfHom
{ Returns whether sheaf S is isomorphic to a Serre twist T(d) of T, another sheaf
  on the same base scheme. If so, the twist d and an isomorphism of degree d are also 
  returned.}

    return find_isomorphism(S,T,true);

end intrinsic;

intrinsic IsIsomorphic(S::ShfCoh,T::ShfCoh) -> BoolElt, ShfHom
{ Returns whether sheaves S and T on the same base scheme are isomorphic. 
  If so, an isomorphism between them is also returned.}

    boo,d,im := find_isomorphism(S,T,false);
    if boo and (d eq 0) then
	return true,im;
    else
	return false,_;
    end if;

end intrinsic;

/////////// zeroes of section ///////////////////////////////////

intrinsic ZeroSubscheme(S::ShfCoh,s::ModMPolElt) -> Sch
{ S should be a locally free sheaf (this is not checked) of scheme X and s
  a homogeneous element of the defining, full or global section module of S,
  representing a global section of a twist S1 of S.
  Returns the zero subscheme of s, i.e. the largest subscheme of X on
  which s pulls back to the zero section of the pullback of S1. }

    M := Parent(s);
    require IsIdentical(M,S`M) or (assigned S`Mfull and IsIdentical(M,S`Mfull)) or
	(assigned S`M0 and IsIdentical(M,S`M0)):
    "Parent of argument 2 must be the defining, maximal or global section module of argument 1";
    require IsHomogeneous(s) : 
	"Argument 2 must be a homogeneous element of its parent module";

    wts := ColumnWeights(M);
    X := S`X;
    if (#wts eq 0) or IsZero(s) then return X; end if; //S is the zero sheaf or s is 0

    // find the degree d of s
    sseq := Eltseq(s);
    assert #sseq eq #wts;
    n := #wts;
      // Assume that sseq contains homogeneous entries. If it's
      // a normal form w.r.t. the relation module of M, this will be true.
      // But is this guaranteed???
    i := [j : j in [1..n] | sseq[j] ne 0][1];
    d := TotalDegree(sseq[i])+wts[i];

    //if R =k[x1,..xn] is the coordinate ring of the ambient of X and I
    // its ideal, and M has presentation F1 -> F0 -> M -> 0 by free R modules
    // (-> pres of free R/I mods), compute the kernel of the dual
    // map F0* -> F1* where Fi* = Hom(Fi,R/I)
    rmat := Transpose(RelationMatrix(M));
    Saturate(~X);
    R := CoordinateRing(Ambient(X));
    B := MinimalBasis(Ideal(X));
    m := #B;
    r := Ncols(rmat);
    N := m*r;
    if N gt 0 then
	mati := Matrix(R,1,m,B);
	mati1 := mati;
	for j in [2..r] do mati1 := DiagonalJoin(mati1,mati); end for;
	mati1 := Transpose(mati1);
	rmat := VerticalJoin(rmat,mati1);
	delete mati1;
    end if;
    if r gt 0 then
      M1 := sub< F| [F!r : r in RowSequence(rmat)]> where F is Module(R,r);
      B1 := Basis(SyzygyModule(M1));
      if N gt 0 then
	r1 := Nrows(rmat)-N;
	B1 := [b1 : b in B1 | &or[e ne 0 : e in b1] where b1 is Eltseq(b)[1..r1] ];
      else
	B1 := [Eltseq(b) : b in B1];
      end if;
      seq := Eltseq(Matrix(B1)*Matrix(#wts,1,sseq));
    else
      seq := sseq;
    end if;
    return Scheme(X,seq);

end intrinsic;
