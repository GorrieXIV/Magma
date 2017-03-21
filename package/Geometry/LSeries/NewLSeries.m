
freeze;

Q:=Rationals(); Z:=Integers();

declare type LSerMot;
declare attributes LSerMot : oldL; // and old L-func version
declare attributes LSerMot : cffunc;
declare attributes LSerMot : sign;
declare attributes LSerMot : cond,hodge,wt; /* prec is in bits */
declare attributes LSerMot : bprec,dprec; /* prec is in bits */
declare attributes LSerMot : coeffvec,coeffbprec,exact_coeffs;
declare attributes LSerMot : parent,name,prod,is_zeta;

// ibp is bp plus guard bits, takes into account error internal to G,phi
// bp is bprec plus guard bits, takes into account error from sums over G,phi
// so bp would be prec plus size of Phi(1/Sqrt(N)) or so

////////////////////////////////////////////////////////////////////////

declare attributes LSerMot : Vp,GS,E,O,mE,mO; // never reset

function get_Vp(SH) d:=#SH; Z:=Integers(); Q:=Rationals();
 P:=PolynomialRing(Q,d); S:=SFA(Q:Basis:="Elementary");
 SUMS:=[1] cat [Evaluate(P!S.[u],SH) : u in [1..d]];
 TILDE:=[&+[(-SUMS[2])^k*d^(m-1-k)*Binomial(k+d-m,k)*SUMS[m-k+1] : k in [0..m]]
	    : m in [0..d]] cat [0];
 A:=FunctionField(Q); x:=A.1; B:=PowerSeriesRing(A,d+3); t:=B.1;
 f:=(Sinh(t)/t)^x; DELTA:=Coefficients(f); C:=PolynomialRing(Q); n:=C.1;
 Vp:=[-d/(2*d)^p*&+[TILDE[m+1]*&*[Z|(d-j) : j in [m..p-1]]*
      &+[(2*n-p+1)^(p-m-k)/Factorial(p-m-k)*Evaluate(DELTA[k+1],d-p) :
	 k in [0..p-m]] : m in [0..p]] : p in [2..d+1]]; // p is shifted
 return [Polynomial([0,-1])] cat Vp cat [0]; end function;

declare attributes LSerMot : cE,cO,bp,gbpow,gbcf; // can reset by prec change

procedure reset_bp(L) L`bp:=0; L`gbpow:=5; L`gbcf:=5; end procedure;

procedure ensure_cEcO(L,b,gb) sE:=L`E; sO:=L`O; S:=sE cat sO;
 if b gt L`bp or b+gb gt L`bp+L`gbpow then  L`bp:=b; L`gbpow:=gb;
  if #L`E ne 0 then e:=&*[GammaHalfSeries(sh+L`mE,#sE,b+gb) : sh in S];
   L`cE:=[Evaluate(e,Parent(e).1/2)]; end if;
  if #L`O ne 0 then e:=&*[GammaHalfSeries(sh+L`mO,#sO,b+gb) : sh in S];
   L`cO:=[Evaluate(e,Parent(e).1/2)]; end if; end if; end procedure;
 // GHS not correct: high terms in prec ?

////////////////////////////////////////////////////////////////////////

function doit_phi_ps(L,b,gb,t) assert gb gt 0; sE:=L`E; sO:=L`O; S:=sE cat sO;
 RF:=RealField(b:Bits); t:=RealField(b+gb : Bits)!t; A:=0; ensure_cEcO(L,b,gb);
 if #sE ne 0 then ev:=LSeriesPhiComputationPowSer(L`cE,S,L`mE,gb,t);
  if ev eq 0 then return RF!doit_phi_ps(L,b,gb+5,t); end if; A:=A+ev; end if;
 if #sO ne 0 then ev:=LSeriesPhiComputationPowSer(L`cO,S,L`mO,gb,t);
  if ev eq 0 then return RF!doit_phi_ps(L,b,gb+5,t); end if; A:=A+ev; end if;
 return RF!A; end function; // keep track of number of guard bits used

intrinsic LPhi_powser(L::LSerMot,t::FldReElt) -> FldReElt {}
 return doit_phi_ps(L,Precision(t:Bits),L`gbpow,t); end intrinsic;

declare attributes LSerMot : Mn,MnCFc,MnCFv;

procedure clear_Mn(L) L`Mn:=[Q|1]; L`MnCFc:=[Q|]; L`MnCFv:=[Z|]; end procedure;

function doit_phi_CF_deg1(LS,gb,t) Rt:=Parent(t);
 t:=RealField(Precision(t:Bits)+gb : Bits)!t;
 return Rt!(2*Exp(-t^2)*t^LS`GS[1]); end function;

function doit_phi_CF_deg2_01(LS,gb,t) Rt:=Parent(t);
 RF:=RealField(Precision(t:Bits)+gb : Bits); t:=RF!t;
 return Rt!(2*Sqrt(Pi(RF))*Exp(-2*t)*t^((-1+&+LS`GS)/2)); end function;

function special_phi_CF(LS)
 if #LS`GS eq 2 and LS`GS[2]-LS`GS[1] eq 1 then return 2; end if;
 if #LS`GS eq 1 then return 1; end if; return 0; end function;

function doit_phi_CF(LS,gb,t) // special case finite contfrac
 if #LS`GS eq 1 then return doit_phi_CF_deg1(LS,gb,t); end if;
 if #LS`GS eq 2 and LS`GS[2]-LS`GS[1] eq 1 then
  return doit_phi_CF_deg2_01(LS,gb,t); end if;
 E:=[* LS`Mn,LS`GS,LS`Vp,LS`MnCFc,LS`MnCFv *];
 ev:=LSeriesPhiComputationContFrac(E,gb,t,10000);
 // note this gives something in t-field, but only to abs t-prec
 if ev eq 0 then return doit_phi_CF(LS,gb+5,t); end if;
 LS`gbcf:=gb; return ev; end function;

intrinsic LPhi_contfrac(L::LSerMot,t::FldReElt) -> FldReElt {}
 return doit_phi_CF(L,L`gbcf,t); end intrinsic;

////////////////////////////////////////////////////////////////////////

declare attributes LSerMot : cancelPhi,tsizePhi,tcrossPhi; // guess, ord of mag
// tsizePhi is t-value where Phi(t) is small enough to be ignored
// tcrossPhi is t-value where contfrac uses no more than 35 terms
// cancelPhi is guess of number of bits that are cancelled at tsizePhi?
// note these are dummies in the [0] and [0,1] cases

function get_tsize_phi(LS) RF:=RealField((LS`bprec div 3)+3*LS`wt : Bits);
 k:=0; reset_bp(LS); l2:=Log(RF!2); // above precision is dodgy!
 deg:=#LS`GS; sc:=1/Sqrt(RF!LS`cond/Pi(RF)^deg); ev:=LPhi_powser(LS,sc);
 while true do k:=k+1; ev2:=LPhi_powser(LS,sc*2^k)*deg*Sqrt(RF!2)^(k*LS`wt);
  if Abs(ev2) lt Abs(ev) then break; else ev:=ev2; end if; end while;
 a:=2^k; b:=2^(k-2); a:=a-b; b:=b/2; // hackish binary splitting
 while b ge 1/2 do ev2:=deg*LPhi_powser(LS,sc*a)*Sqrt(RF!a)^(LS`wt);
  if Abs(ev2) ge Abs(ev) then ev:=ev2; a:=a+b; else a:=a-b; end if;
  b:=b/2; end while;
 a:=2^(k-1); b:=2^(k-3); a:=a-b; b:=b/2;
 while b ge 1/2 do ev2:=deg*LPhi_powser(LS,sc*a)*Sqrt(RF!a)^(LS`wt);
  if Abs(ev2) ge Abs(ev) then ev:=ev2; a:=a-b; else a:=a+b; end if;
  b:=b/2; end while;
 LS`cancelPhi:=3+Ceiling(Max(5,Log(Sqrt(LS`cond))/l2)+Max(0,Log(ev)/l2));
 goal:=LS`bprec+LS`cancelPhi; kappa:=(1-deg+&+LS`GS)/2;
 RHS:=Log(1/2^goal*Sqrt(deg)/2/(2*Pi(RF))^((deg-1)/2));
 f:=func<t|-deg*t^(2/deg)+2*kappa/deg*Log(t)-RHS>; sh:=Infinity();
 g:=func<t|-2*t^(2/deg-1)+2*kappa/deg/t>; t:=(RHS/-deg)^(deg/2);
 while Abs(sh*t) gt 1 do  /* "t",t; */ sh:=f(t)/g(t);
  if sh gt t/2 then t:=t/2; else t:=t-sh; end if; end while;
 sz:=Ceiling(t); LS`tsizePhi:=sz; return sz; end function;

function get_tcross_phi(LS)
 if not assigned LS`tsizePhi then _:=get_tsize_phi(LS); end if; clear_Mn(LS);
 if special_phi_CF(LS) ne 0 then RF:=RealField(LS`bprec+LS`cancelPhi : Bits);
  _:=LPhi_powser(LS,RF!1); LS`tcrossPhi:=RF!1; return RF!1; end if;
 sz:=LS`tsizePhi; RF:=RealField(LS`bprec+LS`cancelPhi : Bits); sc:=1;
 while true do ev:=LPhi_contfrac(LS,RF!sz/sc); // 35 is imperfect...
  if #LS`Mn ge 35 then break; end if; sc:=sc*RF!(6/5); end while;
 cross:=RF!sz/sc; LS`tcrossPhi:=cross;
 _:=LPhi_powser(LS,RealField(LS`bprec+LS`cancelPhi : Bits)!cross); // init
 return cross; end function;

////////////////////////////////////////////////////////////////////////
////////////////////////////////////////////////////////////////////////

declare attributes LSerMot : mun,munCFc,munCFv;

function doit_G_ps(L,b,gb,t,D,s) sE:=L`E; sO:=L`O; S:=sE cat sO;
 RF:=RealField(b:Bits); t:=RealField(b+gb : Bits)!t; A:=0; ensure_cEcO(L,b,gb);
 if #sE ne 0 then ev:=LSeriesGComputationPowSer(L`cE,S,gb,D,s,t);
  if ev eq 0 then return RF!doit_G_ps(L,b,gb+5,t,D,s); end if; A:=A+ev; end if;
 if #sO ne 0 then ev:=LSeriesGComputationPowSer(L`cO,S,-gb,D,s,t); // hack
  if ev eq 0 then return RF!doit_G_ps(L,b,gb+5,t,D,s); end if; A:=A+ev; end if;
 w:=#[g : g in S | s mod 2 eq g mod 2 and s+g le 0]; // worry about s=g
 ev:=&*[GammaHalfSeries(s+g,D+w+1,b+gb) : g in sE cat sO]; S:=Parent(ev).1;
 ev:=Evaluate(ev,S/2); oo:=Coefficient(Derivative(ev/t^S,D),0);
 return RF!(t^(-s)*oo-A); end function; // theo need gbits in final oo-A also

intrinsic LGfunc_powser
(L::LSerMot,t::FldReElt,s::RngIntElt,D::RngIntElt) -> FldReElt {}
 return doit_G_ps(L,Precision(t:Bits),L`gbpow,t,D,s); end intrinsic;

function doit_Gfunc_CF_deg1(LS,gb,t,s) Rt:=Parent(t);
 sc:=Exp(-t^2)*t^(LS`GS[1]-2); sz:=(s+LS`GS[1]-2) div 2;
 return Rt!(sc*&+[Binomial(sz,k)*Factorial(k)/t^(2*k) : k in [0..sz]]);
 end function;

function doit_Gfunc_CF_deg2_01(LS,gb,t,s) Rt:=Parent(t);
 RF:=RealField(Precision(t:Bits)+gb : Bits); t:=RF!t;
 sc:=Sqrt(Pi(RF))*Exp(-2*t)*t^((-3+&+LS`GS)/2); sz:=s+LS`GS[1]-1;
 return Rt!(sc*&+[Binomial(sz,k)*Factorial(k)/2^k/t^k : k in [0..sz]]);
 end function;

function doit_Gfunc_CF(LS,gb,t,s,D) // special case of finite CFs
 if #LS`GS eq 1 and D eq 0 and s mod 2 eq LS`GS[1] mod 2 and s+LS`GS[1] gt 0
  then return doit_Gfunc_CF_deg1(LS,gb,t,s); end if;
 if #LS`GS eq 2 and LS`GS[2]-LS`GS[1] eq 1 and D eq 0 and LS`GS[1] ge 1-s then
  return doit_Gfunc_CF_deg2_01(LS,gb,t,s); end if;
 E:=[* LS`mun,LS`GS,LS`Vp,LS`munCFc[<s,D>],LS`munCFv[<s,D>] *];
 ev:=LSeriesGComputationContFrac(E,gb,s,D,t,10000);
// if ev eq 0 then error "Hit the limit"; end if;
 if ev eq 0 then return doit_Gfunc_CF(LS,gb+5,t,s,D); end if;
 LS`gbcf:=gb; return ev; end function;

intrinsic LGfunc_contfrac
(L::LSerMot,t::FldReElt,s::RngIntElt,D::RngIntElt) -> FldReElt {}
 if not IsDefined(L`munCFc,<s,D>) then L`munCFc[<s,D>]:=[Q|]; end if;
 if not IsDefined(L`munCFv,<s,D>) then L`munCFv[<s,D>]:=[Z|]; end if;
 return doit_Gfunc_CF(L,L`gbcf,t,s,D); end intrinsic;

////////////////////////////////////////////////////////////////////////

procedure reset_munCF(L) // don't reset L`mun
 L`munCFc:=AssociativeArray(); L`munCFv:=AssociativeArray(); end procedure;

procedure reset_mun(L) L`mun:=[PolynomialRing(Q)|1]; // below is <s,D> indexed
 L`munCFc:=AssociativeArray(); L`munCFv:=AssociativeArray(); end procedure;

declare attributes LSerMot : cancelDs,tsizeDs,tcrossDs;

function get_tsize_G(LS,s,D)
 RF:=RealField((LS`bprec div 3)+3*LS`wt : Bits); k:=0; l2:=Log(RF!2);
 // precision dodgy // needs to be s-dependent!
 deg:=#LS`GS; sc:=1/Sqrt(RF!LS`cond/Pi(RF)^deg); ev:=LGfunc_powser(LS,sc,s,D);
 while true do k:=k+1;
  ev2:=LGfunc_powser(LS,sc*2^k,s,D)*deg*Sqrt(RF!2)^(k*LS`wt);
  if Abs(ev2) lt Abs(ev) then break; else ev:=ev2; end if; end while;
 a:=2^k; b:=2^(k-2); a:=a-b; b:=b/2; // hackish binary splitting
 while b ge 1/2 do ev2:=deg*LGfunc_powser(LS,sc*a,s,D)*Sqrt(RF!a)^(LS`wt);
  if Abs(ev2) ge Abs(ev) then ev:=ev2; a:=a+b; else a:=a-b; end if;
  b:=b/2; end while;
 a:=2^(k-1); b:=2^(k-3); a:=a-b; b:=b/2;
 while b ge 1/2 do ev2:=deg*LGfunc_powser(LS,sc*a,s,D)*Sqrt(RF!a)^(LS`wt);
  if Abs(ev2) ge Abs(ev) then ev:=ev2; a:=a-b; else a:=a+b; end if;
  b:=b/2; end while;
 LS`cancelDs[<s,D>]:=3+Ceiling(Max(5,Log(Sqrt(LS`cond))/l2)+Max(0,Log(ev)/l2));
 goal:=LS`bprec+LS`cancelDs[<s,D>]; kappa:=(1-deg+&+LS`GS)/2;
 RHS:=Log(1/2^goal*Sqrt(deg)/(2*Pi(RF))^((deg-1)/2));
 f:=func<t|-deg*t^(2/deg)+2*(kappa-1)/deg*Log(t)-RHS>; sh:=Infinity();
 g:=func<t|-2*t^(2/deg-1)+2*(kappa-1)/deg/t>; t:=(RHS/-deg)^(deg/2);
 while Abs(sh*t) gt 1 do /* "t",t; */ sh:=f(t)/g(t); t:=t-sh; end while;
 sz:=Ceiling(t); LS`tsizeDs[<s,D>]:=sz; return sz; end function;

function special_GsD_CF(LS,s,D)
 if #LS`GS eq 1 and D eq 0 and s mod 2 eq LS`GS[1] mod 2 and s+LS`GS[1] gt 0
  then return 1; end if;
 if #LS`GS eq 2 and LS`GS[2]-LS`GS[1] eq 1 and D eq 0 and LS`GS[1] ge 1-s
  then return 2; end if; return 0; end function;

function get_tcross_G(LS,s,D)
 if not IsDefined(LS`tsizeDs,<s,D>) then _:=get_tsize_phi(LS); end if;
 if special_GsD_CF(LS,s,D) ne 0 then
  RF:=RealField(LS`bprec+LS`cancelDs[<s,D>] : Bits);
  _:=LGfunc_powser(LS,RF!1,s,D); LS`tcrossDs[<s,D>]:=RF!1; return RF!1; end if;
 sz:=LS`tsizeDs[<s,D>]; RF:=RealField(LS`bprec+LS`cancelDs[<s,D>] :Bits); sc:=1;
 while true do ev:=LGfunc_contfrac(LS,RF!sz/sc,s,D); // 35 is imperfect...
  if #LS`munCFc[<s,D>] ge 35 then break; end if; sc:=sc*RF!(6/5); end while;
 cross:=RF!sz/sc; LS`tcrossDs[<s,D>]:=cross;
 _:=LGfunc_powser(LS,RealField(LS`bprec+LS`cancelDs[<s,D>] : Bits)!cross);
 return cross; end function;

////////////////////////////////////////////////////////////////////////

function init_LSMot(GS) L:=New(LSerMot); L`GS:=GS; L`mE:=0; L`mO:=0;
 L`E:=[g : g in GS |g mod 2 eq 0]; if #L`E ne 0 then L`mE:=-Min(L`E)+2; end if;
 L`O:=[g : g in GS |g mod 2 eq 1]; if #L`O ne 0 then L`mO:=-Min(L`O)+2; end if;
 L`Vp:=get_Vp(GS); reset_bp(L); clear_Mn(L); reset_mun(L);
 L`cancelDs:=AssociativeArray(); L`tsizeDs:=AssociativeArray();
 L`tcrossDs:=AssociativeArray(); return L; end function;

////////////////////////////////////////////////////////////////////////

intrinsic LSetPrecision(LS::LSerMot,n::RngIntElt : Bits:=false) {}
 require n ge 1: "Precision must be positive";
 if Bits then LS`bprec:=n; LS`dprec:=Ceiling(LS`bprec*Log(2)/Log(10));
 else LS`dprec:=n; LS`bprec:=Ceiling(LS`dprec*Log(10)/Log(2)); end if;
 reset_bp(LS); clear_Mn(LS); reset_munCF(LS); // keeps mun, resets munCF
 if assigned LS`tsizePhi then delete LS`tsizePhi,LS`tcrossPhi; end if;
 LS`cancelDs:=AssociativeArray(); LS`tsizeDs:=AssociativeArray();
 LS`tcrossDs:=AssociativeArray(); _:=get_tcross_phi(LS); end intrinsic;

////////////////////////////////////////////////////////////////////////

nargs:=func<f|#Split(s,",")-Min(1,Position(s,"()"))-Min(1,Position(s,"( ["))
              where s is Sprint(f)>;
hasprecpar:=func<f|Position(Sprint(f),"[ Precision ]") ne 0>;

procedure make_lsmot_cffunc(L,cf,prec)
 L`exact_coeffs:=not hasprecpar(cf);
 if Type(cf) in [SeqEnum,List] then
  L`cffunc:=function(p,d : Precision:=0)
             if p^d gt #cf then error "Not enough coefficients"; end if;
             A:=[ 1 ] cat [cf[p^i] : i in [1..d]]; // geh, universe
             f:=PowerSeriesRing(Universe(A),d+1)!A;
             return 1/f; end function; return; end if;
 if not Type(cf) eq UserProgram then error "Bad type of coefficents?"; end if;
 if nargs(cf) eq 1 then
  if L`exact_coeffs then
   L`cffunc:=function(p,d : Precision:=0)
              A:=[ 1 ] cat [cf(p^i) : i in [1..d]]; // geh, universe
              f:=PowerSeriesRing(Universe(A),d+1)!A;
              return 1/f; end function; return;
  else
   L`cffunc:=function(p,d : Precision:=prec) // using passed prec variable
              A:=[ 1 ] cat [cf(p^i : Precision:=Precision) : i in [1..d]];
              f:=PowerSeriesRing(Universe(A),d+1)!A;
              return 1/f; end function; return; end if; end if;
 if nargs(cf) eq 2 then
  if L`exact_coeffs then
   L`cffunc:=function(p,d : Precision:=0) return cf(p,d); end function;
   else L`cffunc:=cf; end if; return; end if;
 error "Unable to make coefficient function?"; end procedure;

intrinsic MotivicLSeries(H::HodgeStruc,N::RngIntElt,cf::Any :
			 Precision:=GetPrecision(0.5)) -> LSerMot {}
 require Precision ge 1: "Precision must be at least 1";
 GS:=GammaShifts(H); GS:=Sort(GS);
 if #GS eq 0 then L:=New(LSerMot); L`GS:=GS; return L; end if;
 L:=init_LSMot(GS); L`hodge:=H; L`cond:=N; L`wt:=Weight(H);
 L`parent:=false; L`name:=false; // for now, do this before, in case of error
 make_lsmot_cffunc(L,cf,Precision);
 L`dprec:=Precision; LSetPrecision(L,L`dprec);
 L`coeffvec:=[* *]; L`coeffbprec:=0; L`is_zeta:=false; L`prod:=false;
 if #GS eq 1 and N eq 1 then L`is_zeta:=true; end if;
 L`oldL:=LSeries(H,N,cf : Precision:=Precision); return L; end intrinsic;

intrinsic MotivicLSeries(LO::LSer) -> LSerMot
{Turn a Lser into an LSerMot}
 if LO`prod cmpne false then
  return MotivicLProduct([<MotivicLSeries(l[1]),l[2]> : l in LO`prod]); end if;
 L:=MotivicLSeries(HodgeStructure(LO),Conductor(LO),
		   LO`cffun :Precision:=LO`precision);
 L`parent:=LO`parent; L`name:=LO`name; L`oldL:=LO; return L; end intrinsic;

////////////////////////////////////////////////////////////////////////

function ToSeries(c,d)
 B:=Type(c) in [RngUPolElt,FldFunRatUElt,RngSerPowElt,RngSerLaurElt]
    select BaseRing(Parent(c)) else Parent(c);return PowerSeriesRing(B,1+d)!c;
 end function;

procedure coeffs_from_local_factors(~V,f,B,freq,bprec)
 have:=#V; last_print:=0; Z:=Integers();
 prec:=Ceiling(Log(2)/Log(10)*bprec);
 if have eq 0 then V:=[* 1 :k in [1..B] *]; have:=1;
 else V cat:=[* 1 :k in [have+1..B] *]; end if;
 for p in PrimesUpTo(B) do d:=Ilog(p,B); A:=[* 0 : i in [1..d] *];
  if p ge last_print+freq then last_print:=p;
   vprint LSeries,3:
   Sprint(p)*"/"*Sprint(B)*" ["*Sprint(Round(100*p/B))*"%]"; end if;
  if Ilog(p,B) eq Ilog(p,have) then
   c:=1/ToSeries(Polynomial([V[p^u] : u in [0..Ilog(p,have)]]),d);
  else c:=f(p,d: Precision:=prec); end if;
  S:=1/ToSeries(c,d); for j in [1..d] do A[j]:=Coefficient(S,j); end for;
  // this should only need the ToSeries when Ilog differ
  for j in [1..d] do if IsCoercible(Z,A[j]) then A[j]:=Z!A[j]; end if; end for;
  for k in [1..d] do pk:=p^k; for j in [Ceiling(have/pk)..Floor(B/pk)] do
   if j mod p eq 0 or j*pk le have then continue; end if;
   V[j*pk]*:=A[k]; end for; end for; end for; end procedure;

// don't like hasprecpar : should be a flag like "exact coeffs"
procedure ensure_coeffs(LS,LIM : BitPrecision:=0)
 if LS`exact_coeffs then BitPrecision:=0; end if;
 if #LS`coeffvec ge LIM and LS`coeffbprec ge BitPrecision then return; end if;
 coeffs_from_local_factors(~LS`coeffvec,LS`cffunc,LIM,1000,BitPrecision);
 LS`coeffbprec:=BitPrecision; end procedure; // assume local factors

function cfsz(L,n) omega:=2; return #L`GS^omega*n^(L`wt/2); end function;
// omega is dodgy, max #primefac, though (very) unlikely get Deg from each

function lcf_required(L) // basically a guess
 if L`prod cmpne false then // product
  lr:=Max([LCfRequired(t[1]: Precision:=Precision): t in L`prod] cat [0]);
  return lr; end if; 
 d:=#L`GS; if d eq 0 then return 1; end if;
 expfactor:=Sqrt(L`cond/Pi(RealField(L`dprec))^#L`GS);
 expdifff:=(1+&+L`GS)/d-1; asympconstf:=2*&*[Gamma(k/d):k in [1..d]];
 err:=0.1^(L`dprec)/10/Sqrt(L`cond); t1:=0; t2:=2;
 repeat t:=(t1 ne 0 select (t1+t2)/2 else t2); tt:=t/expfactor;
  res:=cfsz(L,t)*asympconstf*Exp(-d*tt^(2/d))*tt^expdifff;
  if t1 ne 0 then if res gt err then t1:=t; else t2:=t; end if;
  else if res lt err then t1:=t2/2; else t2:=2*t2; end if; end if;
  until t2-t1 le 1; return Ceiling(t2); end function;

// L is LSerMot, t is rational // needs to be ComplexField in general...
// TODO: LGetCoefficients, Coefficient
function LThetaLIM(L,t,wbp,SELF_DUAL) assert t ge 1/5 and t le 5;
 CFR:=lcf_required(L); step:=Max(10,Ceiling(CFR/100)); lim:=0;
 err:=2^(-wbp); eps:=err/10/Sqrt(CFR); wanted_eps_recip:=1/eps;
 curr_bprec:=Ceiling(-Log(eps)/Log(2));
 RF:=RealField(curr_bprec : Bits); RR:=RF;
 if SELF_DUAL then res:=RR!0; else res:=ComplexField(RR)!0; end if;
 exp_decay:=1/Sqrt(RR!L`cond/Pi(RR)^#L`GS);
 while true do ensure_coeffs(L,lim+step : BitPrecision:=curr_bprec);
  for k in [lim+1..lim+step] do
   c:=L`coeffvec[k]; if c eq 0 then continue; end if;
   if k eq 1 then last_phi:=LPhi_powser(L,t*exp_decay); end if;
   while true do // silly while-loop to get precision fix when not OK
    needed_eps_recip:=wanted_eps_recip*Abs(c)*last_phi;
    // "HI",k,needed_eps_recip;
          // should not need a Abs(c) rescaling? though will for G-func
          // think about high weight and LTheta size later...
    working_bprec:=Max(10,1+Ilog(2,Ceiling(needed_eps_recip)));
    RF:=RealField(working_bprec : Bits);
    // huh, how does RF get used? ??!
    if working_bprec gt curr_bprec then
     curr_bprec:=working_bprec; RR:=RealField(curr_bprec:Bits);
     ensure_coeffs(L,lim+step : BitPrecision:=curr_bprec);
     if SELF_DUAL then res:=RR!res; else res:=ComplexField(RR)!res; end if;
     exp_decay:=1/Sqrt(RR!L`cond/Pi(RR)^#L`GS); end if;
    v:=k*t*RR!exp_decay; // think RF is right here, geh...
    if v gt L`tcrossPhi then new_phi:=LPhi_contfrac(L,v);
    else new_phi:=LPhi_powser(L,v); end if;
    new_phi:=RR!new_phi; /* "BYE", v,new_phi; */
    if Abs(new_phi) lt 1.000001*Abs(last_phi) then break; end if;
    last_phi:=new_phi; end while;
   c:=Parent(res)!c; res+:=c*new_phi; /* k,c*new_phi,res; */
   last_phi:=new_phi; end for;
  lim:=lim+step; vprint LSeries,3: "ThetaLIM: "*Sprint(lim)*"/"*Sprint(CFR);
  if cfsz(L,lim)*last_phi lt eps*Abs(res) then break; end if;
// should be looser? Could get more throwaway terms in general...
  end while; vprint LSeries,2: "ThetaLIM Done: "*Sprint(lim)*"/"*Sprint(CFR);
 return res; end function;
// should return something correct to precision wbp
// expected size of LTheta is sqrt(C)^((w+1)/2)
// hmm, not true? maybe depends on phi-behavior at zero

function is_self_dual(L : coeff:=20,bprec:=L`bprec)
 ensure_coeffs(L,coeff : BitPrecision:=bprec);
 C:=L`coeffvec[1..coeff]; CF:=ComplexField(bprec : Bits); 
 return &and[Abs(Imaginary(CF!c)) le 10*2^(-bprec)*Abs(CF!c) : c in C];
 end function;

intrinsic CheckFunctionalEquation(L::LSerMot : t:=11/10,Extra:=0) -> FldReElt
{New version of CheckFunctionalEquation}
 require Type(t) in {FldRatElt,RngIntElt}: "t must be in Q or Z";
 require t ge 1 and t le 5: "t must satisfy 1 <= t <= 5";
 if L`prod cmpne false then
  err:=Max([CheckFunctionalEquation(F[1]: t:=t): F in L`prod] cat [0]);
  L`sign:=IsEmpty(L`prod) select 1 else &*[(F[1]`sign)^F[2]: F in L`prod];
  return err; end if;
 if #L`GS eq 0 then return 0; end if; // case of LSeries(1)
 if L`is_zeta then return 0; end if; // case of deg 1 and conductor 1
 SELF_DUAL:=is_self_dual(L);
 bp:=L`bprec+Extra; wt:=L`wt; lhs:=LThetaLIM(L,t,bp,SELF_DUAL);
 rhs:=ComplexConjugate(LThetaLIM(L,1/t,bp,SELF_DUAL)*t^(-wt-1));
 //  rhs,lhs,Extra; // could be that lhs and/or rhs has more bitprec than bp
 bits:=Min(Precision(lhs:Bits),Precision(rhs:Bits));
 // LTheta should be about size sqrt(C)^((w+1)/2) I think ?
 if Max(Abs(lhs),Abs(rhs)) lt 2^(bp-bits-Extra)
    and Abs(lhs/rhs) lt 1.1 and Abs(lhs/rhs) gt 0.9
  then t:=t*11/10; vprintf LSeries: "Try new t=%o %o %o\n",t,lhs,rhs;
  if t gt 5 then error "Non-convergent in CFENew?"; end if;
  extra:=Ceiling(-Log(Max(Abs(lhs),Abs(rhs))/2^(bp-bits))/Log(2))+1;
  cfe:=CheckFunctionalEquation(L : t:=t,Extra:=extra); return cfe; end if;
 CF:=ComplexField(L`dprec); L`sign:=CF!(lhs/rhs);
 return Abs(Abs(L`sign)-1); end intrinsic;

////////////////////////////////////////////////////////////////////////

function ToSeries(c,d)
 B:=Type(c) in [RngUPolElt,FldFunRatUElt,RngSerPowElt,RngSerLaurElt]
  select BaseRing(Parent(c)) else Parent(c); return PowerSeriesRing(B,1+d)!c;
 end function;

intrinsic IsOne(L::LSerMot) -> BoolElt {True when the degree of L is 0}
 return #L`GS eq 0; end intrinsic;

intrinsic Factorization(L::LSerMot) -> SeqEnum[Tup]
{If an L-series is known to be a product of other L-series,
  return them and their exponents [<L1,n1>,...]. Otherwise returns [<L,1>]}
 return L`prod cmpeq false select [<L,1>] else L`prod; end intrinsic;

function Lprodtermprint(L,n,star)
 if n eq 1 then return star select <"(",L,") * "> else <"(",L,")">;
 else return <"(",L,Sprintf(")^%o%o",n,star select " * " else "")>; end if;
 end function;

procedure SimplifyProduct(~P) n:=1;
 while n lt #P do ind:=[i: i in [1..#P] | P[i][1] eq P[n][1]];
 if #ind gt 1 then exponent:=&+[P[i][2]: i in ind]; P[ind[1]][2]:=exponent;
  if exponent eq 0 then n:=n-1; else Remove(~ind,1); end if;
  else ind:=[]; end if;
  for i in Reverse(ind) do Remove(~P,i); end for; n+:=1; end while;
 end procedure;

procedure SimplifyLProduct(~L) // look for repeated factors
 if L`prod cmpeq false then return; end if;
 SimplifyProduct(~L`prod); P:=L`prod;
 if IsEmpty(P) then L`parent:=1; L`name:=1; L`cond:=1; return; end if;
 L`parent:=<<F[1]`parent,F[2]>: F in P>;
 L`name:=<Lprodtermprint(P[i,1],P[i,2],i ne #P): i in [1..#P]>;
 L`cond:=&*[(F[1]`cond)^F[2]: F in P];
 // L`sign:=&*[(F[1]`sign)^F[2]: F in P]; L`lpoles:=&cat[F[1]`lpoles: F in P];
end procedure;

intrinsic '*'(L1::LSerMot, L2::LSerMot) -> LSerMot
{Product of two motivic L-series}
 if IsOne(L1) then return L2; end if; if IsOne(L2) then return L1; end if;
 require L1`wt eq L2`wt: "L-functions must be the same weight";
 precision:=Min(L1`dprec,L2`dprec);
 function cf(p,d : Precision:=precision)
  f:=ToSeries((L1`cffunc)(p,d : Precision:=Precision),d)*
     ToSeries((L2`cffunc)(p,d : Precision:=Precision),d); return f;
  end function; 
 L:=MotivicLSeries(L1`hodge+L2`hodge,L1`cond*L2`cond,cf :Precision:=precision);
 L`parent:=<L1`parent,"*",L2`parent>; L`name:=<L1," * ",L2>;
 L`prod:=Factorization(L1) cat Factorization(L2);
 SimplifyLProduct(~L); return L; end intrinsic;

intrinsic '^'(L::LSerMot,n::RngIntElt) -> LSerMot
{Take a power of a motivic L-series}
 require n ge 0: "Power of L-Series must be nonnegative";
 if n eq 0 then return MotivicLSeries([],1,0 : Precision:=L`dprec); end if;
 if IsOne(L) then return MotivicLSeries([],1,0 : Precision:=L`dprec); end if;
 if n eq 1 then return L; end if;
 function coeff_func(p,d: Precision:=L`dprec)
  return ToSeries(L`cffunc(p,d : Precision:=Precision),d)^n; end function;
 LS:=MotivicLSeries(n*L`hodge,L`cond^n,coeff_func : Precision:=L`dprec);
 if L`prod cmpeq false then LS`prod:=[<L,n>];
  else LS`prod:=[<a[1],a[2]*n> : a in L`prod]; end if;
 SimplifyLProduct(~LS); return LS; end intrinsic;

intrinsic MotivicLProduct(L::SeqEnum[LSerMot] : Precision:=0) -> LSerMot
{ Return the product of a sequence of L-series}
 return MotivicLProduct([<a,1> : a in L]); end intrinsic;

intrinsic MotivicLProduct(A::SeqEnum[Tup]) -> LSerMot
{ Return the product of a sequence of L-series, given as <L,n> tuples}
 require &and[#a eq 2 : a in A] and &and[Type(a[1]) eq LSerMot : a in A]
         and &and[Type(a[2]) eq RngIntElt and a[2] ge 0 : a in A]:
         "LProduct must be given an array of <L,n> pairs with n ge 0";
 if #A eq 0 then return LSeries(1 : Precision:=GetPrecision(1.2)); end if;
 if #A eq 1 then return '^'(A[1][1],A[1][2]); end if;
 prec:=Min([a[1]`dprec : a in A]);
 function coeff_func(p,d: Precision:=prec) // probably need ToSeries ??
  F:=&*[ToSeries((a[1]`cf)(p,d : Precision:=Precision),d)^a[2] : a in A];
  return F; end function;
 LS:=MotivicLSeries(&+[a[2]*(a[1]`hodge) : a in A],
		    &*[a[1]`cond^a[2] : a in A],coeff_func : Precision:=prec);
 LS`prod:=&cat[[<x[1],x[2]*a[2]> : x in Factorization(a[1])] : a in A];
 SimplifyLProduct(~LS); return LS; end intrinsic;

intrinsic '/'(L1::LSerMot, L2::LSerMot) -> LSerMot
{Quotient of two motivic L-series. It is not checked whether this is valid}
 if IsOne(L2) then return L1; end if;
 require L1`wt cmpeq L2`wt: "Cannot divide L-series: different weights";
 require L1`cond mod L2`cond eq 0: "Conductors do not divide";
 prec:=Min(L1`dprec,L2`dprec);
 function cf(p,d : Precision:=prec) // need ToSeries
  f:=ToSeries((L1`cffunc)(p,d : Precision:=Precision),d)/
     ToSeries((L2`cffunc)(p,d : Precision:=Precision),d); return f;
  end function; 
 L:=MotivicLSeries(L1`hodge-L2`hodge,Integers()!(L1`cond/L2`cond),
		   cf : Precision:=prec);

 L`name:=<L1," / ",L2>; L`parent:=<L1`parent,"/",L2`parent>;
 fact1:=L1`prod cmpeq false select [<L1,1>] else L1`prod;
 fact2:=L2`prod cmpeq false select [<L2,-1>] else [<x[1],-x[2]>: x in L2`prod];
 fact:=fact1 cat fact2; SimplifyProduct(~fact);
 if forall{x: x in fact | x[2] gt 0} then
   L`prod:=fact; SimplifyLProduct(~L); end if;
 SimplifyLProduct(~L); return L; end intrinsic;

////////////////////////////////////////////////////////////////////////

function LSerMotParentCompare(P1,P2)
 if P1 cmpeq false or P2 cmpeq false then return false; end if;
 if Type(P1) ne Type(P2) then return false; end if;
 if Type(P1) eq ModFrmElt and Degree(BaseRing(P1)) ne 1
  then return false; end if;
 if Type(P2) eq ModFrmElt and Degree(BaseRing(P2)) ne 1
  then return false; end if;
 if Type(P1) eq CrvEll and
  BaseRing(P1) eq Rationals() and BaseRing(P2) eq Rationals() then
 b:=IsIsogenous(P1,P2); return b; end if; return P1 cmpeq P2; end function;

intrinsic 'eq'(L1::LSerMot, L2::LSerMot) -> BoolElt
{true iff L1 and L2 are L-series associated to the same object,
 except false for modular forms over number fields, and isogenous
 elliptic curves over Q are also checked}
 if (L1`prod cmpne false) or (L2`prod cmpne false) then
  P1:=L1`prod cmpne false select L1`prod else [<L1,1>];
  P2:=L2`prod cmpne false select L2`prod else [<L2,1>];
  return Set(P1) eq Set(P2); end if;
 if (L1`parent cmpeq false) and (L2`parent cmpeq false)
  then return false; // return L1 cmpeq L2;
 else return LSerMotParentCompare(L1`parent,L2`parent); end if; end intrinsic;

intrinsic 'ne'(L1::LSerMot, L2::LSerMot) -> BoolElt
{true iff L1 and L2 are not associated to the same object,
 except always true for modular forms over number fields,
 and isogenous elliptic curves over Q are always checked}
 return not (L1 eq L2); end intrinsic;

function lsermot_string(L,level)
 if Type(L) eq MonStgElt then return L; end if;
 if Type(L) eq Tup then S:="";
 for i:=1 to #L do
   if Type(L[i]) ne MonStgElt and Type(L[i]) ne Tup and Type(L[i]) ne LSerMot
    then S*:=Sprint(L[i],level); else S*:=lsermot_string(L[i],level); end if;
   end for; return S; end if;
 if Type(L) ne LSerMot then return Sprint(L,level); end if;
 if (level eq "Magma") and (Type(L`name) ne Tup) then
  return Sprintf("MotivicLSeries(%o)",Sprint(L`parent,"Magma")); end if;
 if Type(L`name) ne Tup then
  return Sprintf("Motivic L-series of %o",Sprint(L`name,level)); end if; S:="";
 for i:=1 to #L`name do
  if Type(L`name[i]) ne MonStgElt and Type(L`name[i]) ne Tup
   and Type(L`name[i]) ne LSer then S*:=Sprintf("%o",Sprint(L`name[i],level));
  else S*:=lsermot_string(L`name[i],level); end if; end for;
 return S; end function;

// need both name and parent

procedure PrintTuple(L,level) // lser_string "fixes" part of newline problem
 gc:=GetColumns(); SetColumns(0); S:=lsermot_string(L,level);
 SetColumns(gc); printf "%o",S; return; end procedure;

intrinsic Print(L::LSerMot, level::MonStgElt) {}
 PrintTuple(L,level); end intrinsic;

intrinsic IsCoercible(x::LSerMot, y::.) -> BoolElt, . {}
 return false, _; end intrinsic;

intrinsic 'in'(x::LSerMot, y::.) -> BoolElt {} return false; end intrinsic;



/*
> Attach("/magma/watkins/package/Geometry/LSeries/NewLSeries.m");
LS,L:=NewLSeries(HodgeStructure(3,[0,1,0,1,-1,0]),1234567);

Attach("/magma/watkins/package/Geometry/LSeries/NewLSeries.m");
LS,L:=LSMot([0,0]);
LGfunc_powser(LS,10.0,2,0);
LGfunc_contfrac(LS,10.0,0,0);


// check [0,1] and deg 1 cases
> LS,L:=LSMot([0]);
A:=[LPhi_powser(LS,RealField(30)!t/10) : t in [1..40]];
B:=[LPhi_powser(LS,RealField(40)!t/10) : t in [1..40]];
assert Max([Abs((A[i]-B[i])/A[i]) : i in [1..40]]) le 10^(-29);

Test: check powser at a bunch of small places
have sizes of t increase/decrease
cfrac vs powser, etc.

> Attach("/magma/watkins/package/Geometry/LSeries/NewLSeries.m");
function check_LS_phi(E,t) printf "check_LS_phi %o t=%o\n",E,t;
 LS,L:=LSMot(E); eps:=10^(-29);
 A:=[LPhi_powser(LS,RealField(30)!t/5/k) : k in [1..20]];
 B:=[LPhi_powser(LS,RealField(40)!t/5/k) : k in [1..20]];
 max:=Max([Abs((A[i]-B[i])/Max(1,Min(A[i],B[i]))) : i in [1..20]]);
 max; assert max le eps;
 LS,L:=LSMot(E);
 A:=[LPhi_powser(LS,RealField(30)!t/5/k) : k in [20..1 by -1]];
 B:=[LPhi_powser(LS,RealField(40)!t/5/k) : k in [20..1 by -1]];
 max:=Max([Abs((A[i]-B[i])/Max(1,Min(A[i],B[i]))) : i in [1..20]]);
 max; assert max le eps;
 LS,L:=LSMot(E);
 e1:=LPhi_contfrac(LS,RealField(30)!t); e2:=LPhi_contfrac(LS,RealField(40)!t);
 Abs(e1-e2); assert Abs((e1-e2)/Max(1,Min(e1,e2))) lt 10^(-29);
 LS,L:=LSMot(E);
 e1:=LPhi_contfrac(LS,RealField(40)!t); e2:=LPhi_contfrac(LS,RealField(30)!t);
 Abs(e1-e2); assert Abs((e1-e2)/Max(1,Min(e1,e2))) lt 10^(-29);
 e3:=LPhi_powser(LS,RealField(30)!t); e4:=LPhi_powser(LS,RealField(40)!t);
 Abs(e3-e2); assert Abs((e3-e2)/Max(1,Min(e3,e2))) lt 10^(-29);
 Abs(e1-e4); assert Abs((e1-e4)/Max(1,Min(e1,e4))) lt 10^(-39);
return 0; end function;

check_LS_phi([0],5); check_LS_phi([1],5); check_LS_phi([2],5);
check_LS_phi([-1],5); check_LS_phi([-2],5); // deg 1

check_LS_phi([0,0],25); check_LS_phi([0,1],25); check_LS_phi([0,-2],25);
check_LS_phi([1,1],25); check_LS_phi([1,2],25); check_LS_phi([0,-1],25);
check_LS_phi([1,-1],25); // deg 2

check_LS_phi([0,0,0],75); check_LS_phi([0,0,1],75); check_LS_phi([0,1,1],75);
check_LS_phi([1,1,1],75); check_LS_phi([-1,0,0],75); check_LS_phi([-1,0,1],75);

check_LS_phi([0,0,0,0],100); check_LS_phi([0,0,0,1],100);
check_LS_phi([0,0,1,1],100); check_LS_phi([0,1,1,1],100);
check_LS_phi([1,1,1,1],100); check_LS_phi([0,1,-1,0],100);
check_LS_phi([0,1,-2,-1],100); check_LS_phi([0,1,-3,-2],100);

check_LS_phi([0,0,2,1,1,-1],200); // deg 6

> Attach("/magma/watkins/package/Geometry/LSeries/NewLSeries.m");
function check_LS_Gfunc(E,t,s,D)
 printf "check_LS_Gfunc %o t=%o s=%o D=%o\n",E,t,s,D;
 LS,L:=LSMot(E); eps:=10^(-29);
 A:=[LGfunc_powser(LS,RealField(30)!t/5/k,s,D) : k in [1..20]];
 B:=[LGfunc_powser(LS,RealField(40)!t/5/k,s,D) : k in [1..20]];
 max:=Max([Abs((A[i]-B[i])/Max(1,Min(A[i],B[i]))) : i in [1..20]]);
 max; assert max le eps;
 LS,L:=LSMot(E);
 A:=[LGfunc_powser(LS,RealField(30)!t/5/k,s,D) : k in [20..1 by -1]];
 B:=[LGfunc_powser(LS,RealField(40)!t/5/k,s,D) : k in [20..1 by -1]];
 max:=Max([Abs((A[i]-B[i])/Max(1,Min(A[i],B[i]))) : i in [1..20]]);
 max; assert max le eps;
 LS,L:=LSMot(E);
 e1:=LGfunc_contfrac(LS,RealField(30)!t,s,D);
 e2:=LGfunc_contfrac(LS,RealField(40)!t,s,D);
 Abs(e1-e2); assert Abs((e1-e2)/Max(1,Min(e1,e2))) lt 10^(-29);
 LS,L:=LSMot(E);
 e1:=LGfunc_contfrac(LS,RealField(40)!t,s,D);
 e2:=LGfunc_contfrac(LS,RealField(30)!t,s,D);
 Abs(e1-e2); assert Abs((e1-e2)/Max(1,Min(e1,e2))) lt 10^(-29);
 e3:=LGfunc_powser(LS,RealField(30)!t,s,D);
 e4:=LGfunc_powser(LS,RealField(40)!t,s,D);
 Abs(e3-e2); assert Abs((e3-e2)/Max(1,Min(e3,e2))) lt 10^(-29);
 Abs(e1-e4); assert Abs((e1-e4)/Max(1,Min(e1,e4))) lt 10^(-39);
return 0; end function;

function check_itG(E,t)
 for s in [1..5],D in [0..2] do check_LS_Gfunc(E,t,s-Min(E),D); end for;
 check_LS_Gfunc(E,2*t,10-Min(E),0); check_LS_Gfunc(E,3*t,10-Min(E),1);
 check_LS_Gfunc(E,2*t,1-Min(E),3); check_LS_Gfunc(E,3*t,1-Min(E),4);
 check_LS_Gfunc(E,4*t,1-Min(E),5); return 0; end function;
// needs better scaling with d

check_itG([0],5); check_itG([1],5); check_itG([2],5);
check_itG([-1],5); check_itG([-2],5); // deg 1 slowdown with higher derivs?

check_itG([0,0],25); check_itG([0,1],25); check_itG([0,-2],25);
check_itG([1,1],25); check_itG([0,2],25); check_itG([0,-1],25);
check_itG([1,-1],25); // deg 2

check_itG([0,0,0],75); check_itG([0,0,1],75); check_itG([0,1,1],75);
check_itG([1,1,1],75); check_itG([-1,0,0],75); check_itG([-1,0,1],75);

check_itG([0,0,0,0],100); check_itG([0,0,0,1],100);
check_itG([0,0,1,1],100); check_itG([0,1,1,1],100);
check_itG([1,1,1,1],100); check_itG([0,1,-1,0],100);
check_itG([0,1,-2,-1],100); check_itG([0,1,-3,-2],100);

check_itG([0,0,2,1,1,-1],200); // deg 6 example

*/

/*
L`PhiCaseBound
L`GCaseBound

> L`termstep;
12
> L`lastt;
2108.42681426038777193238942456289487375131962248018732320182859105883486
// should be computable by asymptotics!
termstep is t^(1/3)
  L`expfactor:=Sqrt(RP!L`conductor/Pi(RP)^#L`gamma);
  L`lastt:=L`cfrequired/L`expfactor;

// issue with gbpow for mid-sized t versus small t?

*/
