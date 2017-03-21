
freeze;

declare type GrossenChar;

Z:=Integers();

function cyclo_comp(raw,P) C<i>:=ComplexField(P);
 if Type(Parent(raw)) eq RngInt then return 0; end if;
 m:=Modulus(Parent(raw)); r:=Integers()!raw;
  // zr:=r*(zm div m); return zetam^zr; probably Exp is just as fast
 return Exp(2*Pi(C)*i*(r/m)); end function;

function cyclo_mult(a,b)
 m1:=Modulus(Parent(a)); r1:=Z!a; m2:=Modulus(Parent(b)); r2:=Z!b;
 M:=LCM(m1,m2); r1:=r1*(M div m1); r2:=r2*(M div m2); r:=r1+r2;
 return Integers(M)!r;
 g:=Gcd(M,r); return Integers(M div g)!(r div g); end function;
/* probably want to use second reduction */

////////////////////////////////////////////////////////////////////////

declare attributes GrossenChar: hecke,evalf,type,wt,dirich,zetas,clreps,roots;
declare attributes GrossenChar: field_is_cm;

DelCRs:=func<s|&cat([x: x in Eltseq(Sprint(s)) | x ne "\n"])>; // delete \n's

intrinsic PrintNamed
 (gr::GrossenChar,level::MonStgElt,name::MonStgElt) {Print Grossencharacter}
 if not gr`field_is_cm then
  S:=Sprintf("Tate twist by %o of Hecke character %o in "*
	     "Group of Hecke characters of modulus of norm %o",
	     -gr`wt,gr`hecke,Norm(Modulus(gr`hecke`Parent)));
  oo:=gr`hecke`Parent`ooReal;
  if #oo ne 0 then S*:=Sprintf(" and infinite places %o",oo); end if;
  S*:=Sprintf(" over %o",gr`hecke`Parent`NF);
  printf "%o",DelCRs(S); return; end if;
 S:=Sprintf("Grossencharacter %oof type %o for Hecke-Dirichlet pair "*
	    "(%o,%o) with modulus of norm %o over %o",
	    name ne "$" select name*" " else "",gr`type,
	    gr`hecke,gr`dirich,Norm(Modulus(gr`hecke`Parent)),
	    gr`hecke`Parent`NF);
 printf "%o",DelCRs(S); end intrinsic;

intrinsic IsCoercible (gr::GrossenChar,X::.) -> BoolElt,. {coerce}
 return false,"Illegal coercion"; end intrinsic;

intrinsic 'in' (x::.,gr::GrossenChar) -> BoolElt {in}
 return false; end intrinsic;

// ATTENTION: Unlike the paper, Dirichlet EQUALS oo-type on units, not recip
intrinsic Conductor(gr::GrossenChar) -> RngOrdIdl, SeqEnum
{ Given a Hecke Grossencharacter,
  return its conductor as an ideal and a sequence of real places }
 if not gr`field_is_cm then return Conductor(gr`hecke); end if;
 return Conductor(DirichletRestriction(gr`hecke)/gr`dirich); end intrinsic;

intrinsic Modulus(gr::GrossenChar) -> RngOrdIdl, SeqEnum
{ Given a Hecke Grossencharacter,
  return its modulus as an ideal and a sequence of real places }
 return gr`hecke`Parent`Modulus,gr`hecke`Parent`ooReal; end intrinsic;

intrinsic IsPrimitive(gr::GrossenChar) -> BoolElt
{ Whether or not a Grossencharacter is primitive }
 C,ooC:=Conductor(gr);
 return C eq gr`hecke`Parent`Modulus and ooC eq gr`hecke`Parent`ooReal;
 end intrinsic;

function IsCMField(K)
 d:=Degree(K); r,c:=Signature(K); if r ne 0 then return false; end if;
 if d eq 2 and r eq 0 then return true; end if;
 P:=[F[1] : F in Subfields(K) | 2*Degree(F[1]) eq d and IsTotallyReal(F[1])];
 return #P gt 0; end function;

////////////////////////////////////////////////////////////////////////

declare attributes FldNum: extension_field,Hip,grossen_array,ext_roots;

function cyclo_get_power(z,m)
 if Type(Parent(z)) eq FldRe then z:=ComplexField(Parent(z))!z; end if;
 e:=Round(Real(m*Imaginary(Log(z))/(2*Pi(Parent(z)))));
 if e lt 0 then e:=e+m; end if; return e; end function;

function cyclo_str(z,m)
 return Sprintf("zeta_%o^%o",m,cyclo_get_power(z,m)); end function;

////////////////////////////////////////////////////////////////////////

intrinsic '@'(e::RngIntElt,gr::GrossenChar : Precision:=0) -> RngElt {eval}
 K:=gr`hecke`Parent`NF;
 return '@'(e*IntegerRing(K),gr : Precision:=Precision); end intrinsic;

intrinsic '@'(e::FldRatElt,gr::GrossenChar : Precision:=0) -> RngElt {"} //"
 K:=gr`hecke`Parent`NF;
 return '@'(e*IntegerRing(K),gr : Precision:=Precision); end intrinsic;

intrinsic '@'(e::RngOrdElt,gr::GrossenChar : Precision:=0) -> RngElt {"} //"
 K:=gr`hecke`Parent`NF;
 return '@'(K!e,gr : Precision:=Precision); end intrinsic;

intrinsic '@'(e::FldNumElt,gr::GrossenChar : Precision:=0) -> RngElt {"} //"
 H:=gr`hecke`Parent; K:=Parent(e);
 require K eq H`NF: "Element must be compatible with the character";
 return '@'(e*IntegerRing(K),gr : Precision:=Precision); end intrinsic;

intrinsic '@'
(J::RngOrdFracIdl,gr::GrossenChar : Precision:=0) -> FldComElt {"} //"
 require gr`hecke`Parent`NF eq NumberField(Order(J)):
 "Grossencharacter and ideal must be over the same number field";
 prec:= Precision gt 0 select Precision else GetPrecision(0.5);
 psi:=gr`hecke; v:='@'(J,psi : Raw);
 if Type(Parent(v)) eq RngInt then return ComplexField(prec)!0.0; end if;
 if not gr`field_is_cm then
  return Norm(J)^gr`wt*cyclo_comp('@'(J,gr`hecke : Raw),prec); end if;
 e,z:=gr`evalf(J); r:=ComplexField(prec)!1.0; Hip:=NumberField(Order(J))`Hip;
 for i in [1..#Hip] do
  ip:=Hip[i]; t:=gr`type[i]; ev:=Evaluate(e,ip : Precision:=prec);
  r*:=ev^t[1]*ComplexConjugate(ev)^t[2]; end for;
 return r*cyclo_comp(cyclo_mult(v,z),prec); end intrinsic;

intrinsic RawEval(J::RngOrdFracIdl,gr::GrossenChar) ->
 FldNumElt,FldCycElt,FldCycElt {RawEval}
 require gr`hecke`Parent`NF eq NumberField(Order(J)):
 "Grossencharacter and ideal must be over the same number field";
 if not gr`field_is_cm then return Norm(J)^gr`wt,1,gr`hecke(J); end if;
 v:=gr`hecke(J); if v eq 0 then return 0,0,0; end if;
 e,z:=gr`evalf(J); r:=Z!z; m:=Modulus(Parent(z));
 return e,CyclotomicField(m).1^r,v; end intrinsic;

/************************************************************************/

function AbelianGroupExtension(Q,E,R) // 0 -> E -> A -> Q -> 0
// extend Q by E, with relations R, each <q,m,e> sending m*q to e
 ngQ:=Ngens(Q); ngE:=Ngens(E);
 F:=FreeAbelianGroup(ngQ+ngE);
 REL:=[Order(E.i)*F.(ngQ+i) : i in [1..ngE]];
 fQtoF:=func<q | F ! (Eltseq(q) cat [0 : i in [1..ngE]])>;
 fEtoF:=func<e | F ! ([0 : i in [1..ngQ]] cat Eltseq(e))>;
 FtoQE:=function(e) T:=Eltseq(e);
   return Q![T[i] : i in [1..ngQ]],E![T[i+ngQ] : i in [1..ngE]]; end function;
 S:=[fQtoF(r[1])*r[2]-fEtoF(r[3]) : r in R]; A,qmap:=quo<F|REL cat S>;
 EtoA:=hom<E->A|[qmap(fEtoF(E.i)) : i in [1..ngE]]>;
 AtoQ:=hom<A->Q|[FtoQE((A.i) @@ qmap) : i in [1..Ngens(A)]]>;
 return A,EtoA,AtoQ; end function;

function Principalise(x) b,e:=IsPrincipal(x); assert b; return e; end function;

////////////////////////////////////////////////////////////////////////

procedure grossenideal_catalogue(GI,K) n:=Norm(GI[1]);
 if not n in Keys(K`grossen_array) then K`grossen_array[n]:=<GI>;
 else Append(~K`grossen_array[n],GI); end if; end procedure;

function grossenideal_exists(I,K)
 if not assigned K`grossen_array then
  K`grossen_array:=AssociativeArray(Integers()); return false,_; end if;
 A:=K`grossen_array;
 n:=Norm(I); if not n in Keys(A) then return false,_; end if;
 for gi in A[n] do if gi[1] eq I then return true,gi; end if; end for;
 return false,_; end function;
 
function initialise_grossenideal(I) K:=NumberField(Order(I)); POW:=[]; CLR:=[];
 b,GI:=grossenideal_exists(I,K); if b then return GI; end if; oo:=[]; ROO:=[];
 CL,clmp:=ClassGroup(K); RR,rrm:=RayResidueRing(I,oo); U,um:=UnitGroup(K);
 TOR,tm:=TorsionUnitGroup(K); cyc:=tm(TOR.1);
 H:=K`extension_field; y := PolynomialRing(K).1;
 for i in [1..Ngens(CL)] do c:=clmp(CL.i); m:=MakeCoprime(c,I);
  c:=c*m; CLR cat:=[c]; o:=Order(CL.i);
  e:=(K!(K`ext_roots[i]^o))*m^o; r:=K`ext_roots[i]*m;
  ROO cat:=[r]; POW cat:=[<CL.i,o,e@@rrm>]; end for;
 A,RRtoA,AtoCL:=AbelianGroupExtension(CL,RR,POW); ZE:=[];
 for j in [1..#POW] do o:=POW[j][2];
  mult:=hom<A->A|[o*A.i : i in [1..Ngens(A)]]>; DS,m1,m2:=DirectSum(A,CL);
  h:=hom<A->DS|[m1(mult(A.i))+m2(AtoCL(A.i)) : i in [1..Ngens(A)]]>;
  b,ret:=HasPreimage(m1(RRtoA(POW[j][3]))+m2(POW[j][1]),h); assert b;
  ZE cat:=[ret]; end for;
 DU,dual_map:=Dual(A : UseSameGroup); GI:=<I,CLR,ROO,ZE,0,0,DU,dual_map,RRtoA>;
 grossenideal_catalogue(GI,K); return GI; end function;

procedure ensure_field(K) if assigned(K`extension_field) then return; end if;
 CL,mp:=ClassGroup(K); y := PolynomialRing(K).1; // already comp: HeckeChar
 if #CL eq 1 then K`extension_field:=K; K`ext_roots:=[];
                  K`Hip:=InfinitePlaces(K); return; end if;
 cgp:=[w where _,w:=IsPrincipal(mp(CL.i)^Order(CL.i)) : i in [1..Ngens(CL)]];
 H:=ext<K|[y^Order(CL.i)-cgp[i] : i in [1..Ngens(CL)]]>;
 K`ext_roots:=[Root(H!cgp[i],Order(CL.i)) : i in [1..Ngens(CL)]];
 ip:=[[ooH : ooH in InfinitePlaces(H) | Extends(ooH,ooK)]
           : ooK in InfinitePlaces(K)]; // this should use Decomposition?
 K`extension_field:=H; K`Hip:=[lifts[1] : lifts in ip]; end procedure;

function simple_pullback(e,h)
 o:=Order(e); if o eq 1 then return Domain(h).0; end if;
 H:=Parent(e); HS:=sub<H|e>; S:=HS@@h; G:=Domain(h); A:=sub<G|G.0>;
 for F in Factorization(o) do p:=F[1]; v:=F[2]; W:=Sylow(S,p);
  WS:=sub<W|[W.i : i in [1..Ngens(W)] |  sub<H|h(W.i)> eq (o div (p^v))*HS]>;
  A:=A+sub<G|pPrimaryComponent(WS,p).1>; end for;
 hm:=hom<A->H|[h(G!A.i) : i in [1..Ngens(A)]]>; return G!(e@@hm); end function;

////////////////////////////////////////////////////////////////////////

function get_eval(ZETAS,ROOTS,CLREPS,CHI)
 K:=CHI`Parent`NF; CL,clmp:=ClassGroup(K); ng:=Ngens(CL); H:=K`extension_field;
 function princ_eval(e) b,alpha:=IsPrincipal(e); assert b;
  return K!alpha,-'@'(K!alpha,CHI : Raw); end function;
 function feval(e) im:=-(e@@clmp); expo:=Eltseq(im); zd:=Integers(1)!0;
  mult:=&*[Codomain(clmp) | CLREPS[i]^expo[i] : i in [1..ng]];
  ev,z:=princ_eval(e*mult); dv:=&*[H | ROOTS[i]^expo[i] : i in [1..ng]];
  if ng ne 0 then zd:=&+[ZETAS[i]*expo[i] : i in [1..ng]]; end if;
  return (H!ev)/dv,cyclo_mult(z,zd); end function; return feval; end function;

procedure force_clreps_and_roots(gr,CLREPS,ROOTS,oldchi) ng:=#CLREPS;
 K:=gr`hecke`Parent`NF; CL,clmp:=ClassGroup(K); H:=K`extension_field;
 for i in [1..ng] do // e1*e2 is change in roots, see get_eval above
  e1:=Principalise(CLREPS[i]/gr`clreps[i]); gr`clreps[i]:=CLREPS[i];
  e2:=ROOTS[i]/(gr`roots[i]*e1); gr`roots[i]:=ROOTS[i];
  gr`zetas[i]:=cyclo_mult(gr`zetas[i],'@'(K!(e1*e2),oldchi : Raw)); end for;
 gr`evalf:=get_eval(gr`zetas,gr`roots,gr`clreps,gr`dirich); end procedure;

function make_grossencharacter(chi,psi,I,wt,T)
 K:=NumberField(Order(I)); CL,clmp:=ClassGroup(K); ng:=Ngens(CL);
 GI:=initialise_grossenideal(I); H:=K`extension_field; ID:=Codomain(clmp);
 gr:=New(GrossenChar); gr`wt:=wt; gr`type:=T; gr`field_is_cm:=true;
 gr`clreps:=GI[2]; gr`roots:=GI[3]; ZE:=GI[4];
 Z:=Integers(); DU:=GI[7]; pair:=GI[8]; RRtoA:=GI[9];
 M:=Modulus(Codomain(pair)); CYC:=CyclotomicField(M);
 RR:=Domain(RRtoA); A:=Codomain(RRtoA); AB:=AbelianGroup([M]);
 DS,ic:=DirectSum([AB : i in [1..Ngens(RR)]]);
 h:=hom<DU->DS|
    [&+[ic[j](Domain(ic[j])![Z!pair(DU.i,RRtoA(RR.j))]) : j in [1..Ngens(RR)]]
      : i in [1..Ngens(DU)]]>;
 SD,sp:=Dual(RR : UseSameGroup); m:=Modulus(Codomain(sp)); o:=M div m;
 sd:=SD!Eltseq(chi);
 tar:=&+[ic[j](Domain(ic[j])![o*(Z!sp(sd,RR.j))]) : j in [1..Ngens(RR)]];
 ch:=simple_pullback(tar,h); gr`zetas:=[* pair(ze,ch) : ze in ZE *];
 gr`dirich:=sub<chi`Parent|[chi]>!chi; gr`hecke:=sub<psi`Parent|[psi]>!psi;
 gr`evalf:=get_eval(gr`zetas,gr`roots,gr`clreps,chi); return gr; end function;

////////////////////////////////////////////////////////////////////////

// Evaluate works to KANT prec here !?
function check_1modI_is_OK(I,T) oo:=[]; K:=NumberField(Order(I));
 U,um:=UnitGroup(K); RR,rm:=RayResidueRing(I,oo); ip:=InfinitePlaces(K);
 A:=[ K!um(u) : u in Generators(U) ]; AA:=[ u^Order(u @@ rm) :  u in A ];
 for i in [1..#AA] do ev:=[Evaluate(AA[i],pl) : pl in ip];
  pr:=&*[ev[i]^T[i][1]*ComplexConjugate(ev[i])^T[i][2] : i in [1..#ev]];
  b:=Abs(pr-1) lt 10^(-Precision(pr)/2); if b then continue; end if;
  return false,
    Sprintf("\noo-type should be trivial on all"*
	    " totally positive units that are 1 mod I\n"*
	    "Fails for %o which gives %o\n",K!A[i],ComplexField(10)!pr),K!A[i];
 end for; return true,_,_; end function;

function check_chi_is_OK(chi,T) K:=NumberField(Order(chi`Parent`Modulus));
 U,um:=UnitGroup(K); ip:=InfinitePlaces(K); A:=[K!um(u) : u in Generators(U)];
 MOD:=CyclotomicOrder(chi`Parent`TargetRing);
 for i in [1..#A] do ev:=[Evaluate(A[i],pl) : pl in ip];
  prod:=&*[ev[i]^T[i][1]*ComplexConjugate(ev[i])^T[i][2] : i in [1..#ev]];
  pr:=Precision(prod); b:=Abs(prod-ComplexField(pr)!chi(A[i])) lt 10^(-pr/2);
  if b then continue; end if;
  return false,
    Sprintf("\noo-type must be compatible with Dirichlet character on units\n"*
	    "Fails for %o which gives %o rather than %o\n",K!A[i],
	    cyclo_str(prod,MOD),cyclo_str(ComplexField()!chi(A[i]),MOD));
 end for; return true,_; end function;

function get_chi(I,T) K:=NumberField(Order(I)); oo:=[]; IM:=[];
 U,um:=UnitGroup(K); ip:=InfinitePlaces(K); A:=[K!um(u) : u in Generators(U)];
 DG:=DirichletGroup(I,oo); MOD:=CyclotomicOrder(DG`TargetRing);
 rm:=DG`ResidueMap; RR:=Domain(rm);
 for i in [1..#A] do ev:=[Evaluate(A[i],pl) : pl in ip];
  prod:=&*[ev[i]^T[i][1]*ComplexConjugate(ev[i])^T[i][2] : i in [1..#ev]];
  k:=cyclo_get_power(prod,MOD); r:=A[i]@@rm; IM cat:=[<r,k>]; end for;
 DS,ic:=DirectSum([AbelianGroup([MOD]) : i in [1..#A]]); Z:=Integers();
 h:=hom<DG`AbGrp->DS|
        [&+[ic[i](Domain(ic[i])![Z!DG`Pairing(IM[i][1],RR.j)]) : i in [1..#A]]
	  : j in [1..Ngens(RR)]]>;
 t:=&+[ic[i](Domain(ic[i])!IM[i][2]) : i in [1..#A]];
 b,e:=HasPreimage(t,h); if not b then return false,_; end if;
 e:=simple_pullback(t,h); assert h(e) eq t;
 return true,DG!Eltseq(e); end function;

////////////////////////////////////////////////////////////////////////

intrinsic Grossencharacter(psi::GrpHeckeElt,T::SeqEnum[SeqEnum[RngIntElt]])
 -> GrossenChar
{Given a Hecke character along with a compatible infinity-type,
 try to find a suitable Dirichlet character on the units,
 and then return the induced Hecke Grossencharacter}
 if psi`Parent`issubgroup then
  return Grossencharacter(psi`Parent`supergroup!psi,T); end if;
 K:=psi`Parent`NF; I:=psi`Parent`Modulus; oo:=psi`Parent`ooReal;
 require IsCMField(K): "Field must be of CM-type (use TateTwist for norms)";
 require Degree(K) eq 2*#T: "Degree must equal number of oo-type components";
 require #Set([&+t : t in T]) eq 1: "All oo-type parts must have same weight";
 b,S:=check_1modI_is_OK(I,T); require b: S;
 b,chi:=get_chi(I,T); require b: "No suitable Dirichlet character exists";
 ensure_field(K);
 return make_grossencharacter(chi,psi,I,&+T[1],T); end intrinsic;

intrinsic Grossencharacter
 (psi::GrpHeckeElt,chi::GrpDrchNFElt,T::SeqEnum[SeqEnum[RngIntElt]])
 -> GrossenChar
{Given a Hecke character along with a compatible infinity-type and
 Dirichlet character, return the induced Hecke Grossencharacter}
 if psi`Parent`issubgroup then
  return Grossencharacter(psi`Parent`supergroup!psi,chi,T); end if;
 if chi`Parent`issubgroup then
  return Grossencharacter(psi,chi`Parent`supergroup!chi,T); end if;
 K:=psi`Parent`NF; I:=psi`Parent`Modulus; oo:=psi`Parent`ooReal;
 require K eq chi`Parent`NF: "psi and chi must be defined over same field";
 require I eq chi`Parent`Modulus and oo eq chi`Parent`ooReal:
 "psi and chi must have same modulus";
 require IsCMField(K): "Field must be of CM-type";
 require Degree(K) eq 2*#T: "Degree must equal number of oo-type components";
 require #Set([&+t : t in T]) eq 1: "All oo-type parts must have same weight";
 if Degree(K) gt 2 then "WARNING: Not tested beyond quadratic fields"; end if;
 b,S:=check_1modI_is_OK(I,T); require b: S;
 b,S:=check_chi_is_OK(chi,T); require b: S;
 ensure_field(K);
 return make_grossencharacter(chi,psi,I,&+T[1],T); end intrinsic;

intrinsic GrossenCheck(I::RngOrdIdl,T::SeqEnum[SeqEnum[RngIntElt]]) ->
 BoolElt, FldNumElt
{Given an ideal in a CM field and an oo-type, determine whether
 the oo-type trivialises all units that are 1 mod I}
 K:=NumberField(Order(I)); require IsCMField(K): "Field must be of CM-type";
 require Degree(K) eq 2*#T: "Degree must equal number of oo-type components";
 require #Set([&+t : t in T]) eq 1: "All oo-type parts must have same weight";
 b,_,e:=check_1modI_is_OK(I,T);
 if b then return true,_; else return false,e; end if; end intrinsic;

function GrossenCopy(gr) cp:=New(GrossenChar);
 cp`wt:=gr`wt; cp`type:=gr`type; cp`hecke:=gr`hecke; cp`dirich:=gr`dirich;
 cp`zetas:=gr`zetas; cp`roots:=gr`roots; cp`clreps:=gr`clreps;
 cp`evalf:=gr`evalf; cp`field_is_cm:=gr`field_is_cm; return cp; end function;

////////////////////////////////////////////////////////////////////////

intrinsic '*'(gr::GrossenChar,psi::GrpHeckeElt) -> GrossenChar {Multiply} //"
 require gr`hecke`Parent`NF eq psi`Parent`NF:
 "Grossencharacter and Hecke character must be defined over the same field";
 if not gr`field_is_cm then
  return TateTwist(gr`hecke*psi,-(gr`wt div 2)); end if;
 if psi`Parent`Modulus eq gr`hecke`Parent`Modulus and
    psi`Parent`ooReal eq gr`hecke`Parent`ooReal then
  GR:=GrossenCopy(gr); GR`hecke*:=psi; return GR; end if;
 nh:=gr`hecke*psi; GR:=Extend(gr,Modulus(nh)); GR`hecke:=nh;
 return GR; end intrinsic;

intrinsic '*'(psi::GrpHeckeElt,gr::GrossenChar) -> GrossenChar {"} //"
 require gr`hecke`Parent`NF eq psi`Parent`NF:
 "Grossencharacter and Hecke character must be defined over the same field";
 return '*'(gr,psi); end intrinsic;

intrinsic '*'(gr::GrossenChar,chi::GrpDrchNFElt) -> GrossenChar {"} //"
 require gr`hecke`Parent`NF eq chi`Parent`NF:
 "Grossencharacter and Dirichlet character must be defined over same field";
 return gr*HeckeLift(chi); end intrinsic;

intrinsic '*'(chi::GrpDrchNFElt,gr::GrossenChar) -> GrossenChar {"} //"
 require gr`hecke`Parent`NF eq chi`Parent`NF:
 "Grossencharacter and Dirichlet character must be defined over same field";
 return gr*HeckeLift(chi); end intrinsic;

intrinsic '/'(psi::GrpHeckeElt,gr::GrossenChar) -> GrossenChar {Divide} //"
 require gr`hecke`Parent`NF eq psi`Parent`NF:
 "Grossencharacter and Hecke character must be defined over the same field";
 return psi*(gr^(-1)); end intrinsic;

intrinsic '/'(gr::GrossenChar,psi::GrpHeckeElt) -> GrossenChar {"} //"
 require gr`hecke`Parent`NF eq psi`Parent`NF:
 "Grossencharacter and Hecke character must be defined over the same field";
 return gr*(psi^(-1)); end intrinsic;

intrinsic '/'(chi::GrpDrchNFElt,gr::GrossenChar) -> GrossenChar {"} //"
 require gr`hecke`Parent`NF eq chi`Parent`NF:
 "Grossencharacter and Dirichlet character must be defined over same field";
 return chi*(gr^(-1)); end intrinsic;

intrinsic '/'(gr::GrossenChar,chi::GrpDrchNFElt) -> GrossenChar {"} //"
 require gr`hecke`Parent`NF eq chi`Parent`NF:
 "Grossencharacter and Dirichlet character must be defined over same field";
 return gr*(chi^(-1)); end intrinsic;

////////////////////////////////////////////////////////////////////////

intrinsic '^'(gr::GrossenChar,n::RngIntElt) -> GrossenChar {Power}
 if not gr`field_is_cm then GR:=New(GrossenChar); GR`field_is_cm:=false;
  GR`hecke:=gr`hecke^n; GR`wt:=gr`wt*n; return GR; end if;
 GR:=New(GrossenChar); GR`field_is_cm:=true;
 GR`dirich:=gr`dirich^n; GR`hecke:=gr`hecke^n; GR`wt:=n*gr`wt;
 GR`zetas:=[* x*n : x in gr`zetas *]; GR`roots:=gr`roots; GR`clreps:=gr`clreps;
 GR`type:=[[n*gr`type[i][1],n*gr`type[i][2]] : i in [1..#gr`type]];
 GR`evalf:=get_eval(GR`zetas,GR`roots,GR`clreps,GR`dirich);
 return GR; end intrinsic;

intrinsic '*'(g1::GrossenChar,g2::GrossenChar) -> GrossenChar {Multiply}
 require g1`hecke`Parent`NF eq g2`hecke`Parent`NF:
  "Grossencharacters must be in same field";
 if not g1`field_is_cm then g3:=New(GrossenChar); g3`field_is_cm:=false;
  g3`wt:=g1`wt+g2`wt; g3`hecke:=g1`hecke*g2`hecke; return g3; end if;
 g3:=New(GrossenChar); g3`wt:=g1`wt+g2`wt; g3`field_is_cm:=true;
 g3`dirich:=g1`dirich*g2`dirich; g3`hecke:=g1`hecke*g2`hecke;
 TYPE:=[[g1`type[i][1]+g2`type[i][1],
	 g1`type[i][2]+g2`type[i][2]] : i in [1..#g1`type]];
 g3`type:=TYPE; I:=Modulus(g3`hecke); GI:=initialise_grossenideal(I);
 G1:=GrossenCopy(g1); force_clreps_and_roots(G1,GI[2],GI[3],g1`dirich);
 G2:=GrossenCopy(g2); force_clreps_and_roots(G2,GI[2],GI[3],g2`dirich);
 assert G1`roots eq G2`roots; assert G1`roots eq GI[3];
 ZETAS:=[* cyclo_mult(G1`zetas[i],G2`zetas[i]) : i in [1..#G1`zetas] *];
 CLREPS:=GI[2]; ROOTS:=GI[3];
 g3`zetas:=ZETAS; g3`roots:=ROOTS; g3`clreps:=CLREPS;
 g3`evalf:=get_eval(ZETAS,ROOTS,CLREPS,g3`dirich); return g3; end intrinsic;

intrinsic '/'(g1::GrossenChar,g2::GrossenChar) -> GrossenChar {Divide}
 require g1`hecke`Parent`NF eq g2`hecke`Parent`NF:
 "Grossencharacters must be in same field"; return g1*(g2^(-1)); end intrinsic;

intrinsic '/'(e::RngIntElt,gr::GrossenChar) -> GrossenChar {"} //"
 require e eq 1: "Numerator must be 1"; return gr^(-1); end intrinsic;

////////////////////////////////////////////////////////////////////////

declare attributes GrossenChar : components;

// ATTENTION: Unlike the paper, Dirichlet EQUALS oo-type on units, not recip

intrinsic Components(gr::GrossenChar) -> Assoc
{Given a Grossencharacter, return the components of its Dirichlet-Hecke
 restriction, as an associative array indexed by ramified places}
 if assigned gr`components then return gr`components; end if;
 if not gr`field_is_cm then C:=Components(DirichletRestriction(gr`hecke));
 else C:=Components(DirichletRestriction(gr`hecke)/gr`dirich); end if;
 gr`components:=C; return C; end intrinsic;

intrinsic Component(gr::GrossenChar,P::RngOrdIdl) -> GrpDrchNFElt
{Given a Grossencharacter, return its Dirichlet component at P (a prime ideal)}
 require IsPrime(P): "P must be prime"; K:=gr`hecke`Parent`NF;
 require K eq NumberField(Order(P)):
 "Grossencharacter and P must be defined over same number field";
 C:=Components(gr); P:=Place(P);
 if not P in Keys(C) then return DirichletGroup(1*Integers(K)).0; end if;
 return C[P]; end intrinsic;

intrinsic Component(gr::GrossenChar,oo::RngIntElt) -> GrpDrchNFElt
{Given a Grossencharacter, return its Dirichlet component at an infinite place}
 K:=gr`hecke`Parent`NF; IP:=InfinitePlaces(K); C:=Components(gr);
 require oo ge 1 and oo le #IP: "Invalid infinite place specified"; P:=IP[oo];
 if not P in Keys(C) then return DirichletGroup(1*Integers(K)).0; end if;
 return C[P]; end intrinsic;

intrinsic Component(gr::GrossenChar,p::PlcNumElt) -> GrpDrchNFElt
{Given a Grossencharacter, return its Dirichlet component at a given place}
 K:=gr`hecke`Parent`NF; C:=Components(gr);
 require K eq NumberField(p): "Grossenchar and p must be defined over same NF";
 if not p in Keys(C) then return DirichletGroup(1*Integers(K)).0; end if;
 return C[p]; end intrinsic;

////////////////////////////////////////////////////////////////////////

Z:=Integers();

function oo_eval(GR,alpha : Precision:=GetPrecision(0.5))
 if Type(GR) eq GrpHeckeElt then return 1; end if;
 oo:=GR`type; K:=Parent(alpha); IP:=InfinitePlaces(K);
 ev:=[Evaluate(alpha,pl : Precision:=Precision) : pl in IP];
 return &*[ev[i]^oo[i][1]*ComplexConjugate(ev[i])^oo[i][2] : i in [1..#IP]];
 end function;

function typ_eval(G,I,C,prec)
 if Type(G) eq GrossenChar then return '@'(I,G : Precision:=prec);
 else return C!G(I); end if; end function;

function root_no(GR,P : Precision:=GetPrecision(0.5)) // primitive !!
 q:=Norm(P); _,p,f:=IsPrimePower(q); K:=NumberField(Order(P));
 d:=Valuation(Different(Integers(K)),P); M:=Conductor(GR); e:=Valuation(M,P);
 C:=ComplexField(Precision); z:=2*Pi(C)*C.1; res:=C!0;
 if d eq 0 and e eq 0 then return C!1; end if;
 if e eq 0 then ev:=typ_eval(GR,P^d,C,Precision); return ev/Abs(ev); end if;
 COMP:=Components(GR); ch:=COMP[P]; // no inverse!!
 R,mp:=Completion(K,P : Precision:=f*(2*e+2*d+5)); Q,qm:=quo<Integers(K)|P^e>;
 _,alpha:=IsPrincipal(P^(d+e)*PrincipalMultiple(P^(d+e),M));
 img:=mp(alpha); assert Valuation(img) eq d+e; Qp:=PrimeField(R);
 for b in Q do a:=K!(b@@qm); if Valuation(a,P) ne 0 then continue; end if;
  tr:=Trace(mp(a)/img,Qp);
  c:=IsWeaklyZero(tr) select 0 else (Z!(tr/p^v))*p^v where v:=Valuation(tr);
  res:=res+(C!ch(a))*Exp(z*FractionalPart(c)); end for; res:=res/Sqrt(C!q^e);
 I:=alpha*Integers(K); assert Valuation(I,P) eq d+e;
 A:=I/P^(d+e); assert Norm(Gcd(A,M)) eq 1;
 a:=oo_eval(GR,alpha : Precision:=Precision); b:=typ_eval(GR,A,C,Precision);
 c:=&*[C | COMP[k](alpha) : k in Keys(COMP) | k ne Place(P)]; // recip inverse
 res:=res*a/b*c; return res/Abs(res); end function;

intrinsic RootNumber
(gr::GrossenChar,P::RngOrdIdl : Precision:=GetPrecision(0.5)) -> FldComElt
{Given a Grossencharacter and a prime ideal, return the local root number}
 require IsPrime(P): "P must be prime"; K:=gr`hecke`Parent`NF;
 require K eq NumberField(Order(P)):
 "Grossencharacter and P must be defined over same number field";
 return root_no(AssociatedPrimitiveCharacter(gr),P : Precision:=Precision); 
 end intrinsic;

intrinsic RootNumber
(psi::GrpHeckeElt,P::RngOrdIdl : Precision:=GetPrecision(0.5)) -> FldComElt
{Given a Hecke character and a prime ideal, return the local root number}
 require IsPrime(P): "P must be prime"; K:=psi`Parent`NF;
 require K eq NumberField(Order(P)):
 "psi and P must be defined over same number field";
 return root_no(AssociatedPrimitiveCharacter(psi),P : Precision:=Precision); 
 end intrinsic;

intrinsic RootNumber
(gr::GrossenChar,p::PlcNumElt : Precision:=GetPrecision(0.5)) -> FldComElt
{Given a Grossencharacter and a place, return the local root number}
 require NumberField(p) eq gr`hecke`Parent`NF:
 "Place must be of same number field as Grossencharacter";
 if IsFinite(p) then
  return RootNumber(gr,Ideal(p) : Precision:=Precision); end if;
 if not gr`field_is_cm then
  if IsComplex(p) then return ComplexField(Precision)!1; end if; // q=p
  S:=RealPlaces(gr`hecke`Parent`NF)[[o : o in gr`hecke`Parent`ooReal]];
  if p in S then return -ComplexField(Precision).1; // -zeta_4
  else return ComplexField(Precision)!1; end if; end if;
 IP:=InfinitePlaces(gr`hecke`Parent`NF); w:=Index(IP,p);
 TYPE:=Sort(gr`type[w]); ans:=TYPE[2]-TYPE[1]; // q-p
 return 1/ComplexField(Precision).1^(ans); end intrinsic;

intrinsic RootNumber
(psi::GrpHeckeElt,p::PlcNumElt : Precision:=GetPrecision(0.5)) -> FldComElt
{Given a Hecke character and a place, return the local root number}
 if IsFinite(p) then
  return RootNumber(psi,Ideal(p) : Precision:=Precision); end if;
 if IsComplex(p) then return ComplexField(Precision)!1; end if; // q=p
 S:=RealPlaces(psi`Parent`NF)[[oo : oo in psi`Parent`ooReal]];
 if p in S then return -ComplexField(Precision).1; // -zeta_4
 else return ComplexField(Precision)!1; end if; end intrinsic;

intrinsic RootNumbers
(gr::GrossenChar : Precision:=GetPrecision(0.5)) -> SeqEnum
{Given a Grossencharacter, return the root numbers at bad places}
 C,oo:=Conductor(gr); K:=gr`hecke`Parent`NF;
 F:=Factorization(C*Different(Integers(K)));
 A:=[<Place(f[1]),RootNumber(gr,f[1] : Precision:=Precision)> : f in F];
 if not gr`field_is_cm then
  A cat:=[<p,RootNumber(gr,p :Precision:=Precision)> : p in RealPlaces(K)[oo]];
 else IP:=InfinitePlaces(K); T:=gr`type; prec:=Precision;
  A cat:=[<p,RootNumber(gr,p : Precision:=Precision)> : p in IP]; end if;
 return A; end intrinsic;

intrinsic RootNumbers
(psi::GrpHeckeElt : Precision:=GetPrecision(0.5)) -> SeqEnum
{Given a Hecke character, return the root numbers at bad places}
 C,oo:=Conductor(psi); K:=psi`Parent`NF;
 F:=Factorization(C*Different(Integers(K)));
 A:=[<Place(f[1]),RootNumber(psi,f[1] : Precision:=Precision)> : f in F];
 A cat:=[<p,RootNumber(psi,p :Precision:=Precision)> : p in RealPlaces(K)[oo]];
 return A; end intrinsic;

intrinsic RootNumber
(gr::GrossenChar : Precision:=GetPrecision(0.5)) -> FldComElt
{Given a Grossencharacter, compute its global root number}
 R:=RootNumbers(gr : Precision:=Precision);
 return &*[ComplexField(Precision) | r[2] : r in R];  end intrinsic;

intrinsic RootNumber
(psi::GrpHeckeElt : Precision:=GetPrecision(0.5)) -> FldComElt
{Given a Hecke character, compute its global root number}
 R:=RootNumbers(psi : Precision:=Precision);
 return &*[ComplexField(Precision) | r[2] : r in R];  end intrinsic;

intrinsic RootNumber
(gr::GrossenChar,p::RngIntElt : Precision:=GetPrecision(0.5)) -> FldComElt
{Given a Grossencharacter and a rational prime p, compute its root number}
 require IsPrime(p): "p must be prime"; C:=ComplexField(Precision);
 K:=NumberField(Order(Modulus(gr))); FAC:=Factorization(p*Integers(K));
 res:=&*[RootNumber(gr,P[1])*C!RootNumber(Completion(K,P[1])) : P in FAC];
 return res; end intrinsic;

intrinsic RootNumber
(psi::GrpHeckeElt,p::RngIntElt : Precision:=GetPrecision(0.5)) -> FldComElt
{Given a Hecke character and a rational prime p, compute its root number}
 require IsPrime(p): "p must be prime"; C:=ComplexField(Precision);
 K:=NumberField(Order(Modulus(psi))); FAC:=Factorization(p*Integers(K));
 res:=&*[RootNumber(psi,P[1])*C!RootNumber(Completion(K,P[1])) : P in FAC];
 return res; end intrinsic;

////////////////////////////////////////////////////////////////////////

intrinsic Extend(gr::GrossenChar,I::RngOrdIdl) -> GrossenChar
{Extend a Grossencharacter to the given ideal}
 if not gr`field_is_cm then
  return TateTwist(Extend(gr`hecke,I),-gr`wt); end if;
 require gr`hecke`Parent`NF eq NumberField(Order(I)):
  "Grossencharacter and ideal must be over the same number field";
 require I subset Modulus(gr):
  "The modulus of the new group must be divisible by that of the old";
 // if I eq Modulus(gr) then return gr; end if;
 GR:=GrossenCopy(gr); GR`dirich:=Extend(gr`dirich,DirichletGroup(I));
 GR`hecke:=Extend(gr`hecke,HeckeCharacterGroup(I));
 GR`dirich:=sub<GR`dirich`Parent|[GR`dirich]>!GR`dirich;
 GR`hecke:=sub<GR`hecke`Parent|[GR`hecke]>!GR`hecke;
 GI:=initialise_grossenideal(I); // handles zetas correct from force_clreps ?!
 force_clreps_and_roots(GR,GI[2],GI[3],gr`dirich); return GR; end intrinsic;

intrinsic Extend(gr::GrossenChar,I::RngOrdIdl,oo::SeqEnum[RngIntElt])
 -> GrossenChar
{Extend a Grossencharacter to the given ideal and possible oo places}
 if not gr`field_is_cm then
  return TateTwist(Extend(gr`hecke,I,oo),-gr`wt); end if;
 if #oo eq 0 then return Extend(gr,I); end if;
 require false: "There are no real infinite places, but some were given?";
 end intrinsic;

intrinsic Restrict(gr::GrossenChar,I::RngOrdIdl) -> GrossenChar
{Restrict a Grossencharacter to the given ideal}
 if not gr`field_is_cm then
  return TateTwist(Restrict(gr`hecke,I),-gr`wt); end if;
 require gr`hecke`Parent`NF eq NumberField(Order(I)):
  "Grossencharacter and ideal must be over the same number field";
 require Modulus(gr) subset I:
 "The modulus of the grossencharacter must contain the ideal";
 require I subset Conductor(gr):
 "The ideal must be a subset of the conductor of the grossencharacter";
 GR:=GrossenCopy(gr); dr:=DirichletRestriction(gr`hecke);
 GR`dirich:=Restrict(gr`dirich/DirichletRestriction(gr`hecke),I);
 GR`hecke:=Restrict(gr`hecke/gr`hecke,I); // simplify hecke
 GR`dirich:=sub<GR`dirich`Parent|[GR`dirich]>!GR`dirich;
 GR`hecke:=sub<GR`hecke`Parent|[GR`hecke]>!GR`hecke;
 GR`zetas:=[* cyclo_mult(gr`zetas[i],-'@'(gr`clreps[i],gr`hecke : Raw))
			: i in [1..#gr`clreps] *];
 GR`evalf:=get_eval(GR`zetas,GR`roots,GR`clreps,GR`dirich);
 return GR; end intrinsic;

intrinsic Restrict(gr::GrossenChar,I::RngOrdIdl,oo::SeqEnum[RngIntElt])
 -> GrossenChar
{Restrict a Grossencharacter to the given ideal and possible oo places}
 if not gr`field_is_cm then
  return TateTwist(Restrict(gr`hecke,I,oo),-gr`wt); end if;
 if #oo eq 0 then return Restrict(gr,I); end if;
 require false: "There are no real infinite places, but some were given?";
 end intrinsic;

intrinsic AssociatedPrimitiveGrossencharacter(gr::GrossenChar) -> GrossenChar
{Return the associated primitive Grossencharacter of a given one}
 if IsPrimitive(gr) then return gr; end if;
 C,oo:=Conductor(gr); return Restrict(gr,C,oo); end intrinsic;

intrinsic AssociatedPrimitiveCharacter(gr::GrossenChar) -> GrossenChar {"}//"
 return AssociatedPrimitiveGrossencharacter(gr); end intrinsic;

intrinsic Weight(psi::GrossenChar) -> RngIntElt
{Given a Hecke Grossencharacter, returns its weight}
 if not psi`field_is_cm then return 2*psi`wt; end if;
 return psi`wt; end intrinsic;

intrinsic CentralCharacter(psi::GrossenChar) -> GrpDrchNFElt
{Given a Hecke Grossencharacter, compute its central Dirichlet
 character down to Q (normalised to have weight 0).}
 if not psi`field_is_cm then return CentralCharacter(psi`hecke); end if;
 n:=Norm(Modulus(psi)); Q:=NumberField(Polynomial([-1,1]) : DoLinearExtension);
 G:=DirichletGroup(n*IntegerRing(Q),[1]); // include oo
 mI:=G`ResidueMap; RI:=Domain(mI); reps:=[mI(RI.i) : i in [1..Ngens(RI)]];
 MO:=MaximalOrder(NumberField(Order(Modulus(psi))));
 X:=<<r,(Integers()!Rationals()!((Q!e)/(Q!r)))*
        cyclo_mult('@'(r*MO,psi`hecke : Raw),z)>
        where e,z:=psi`evalf(r*MO) : r in reps>;
 ch:=DirichletCharacter(G,X); ch:=AssociatedPrimitiveCharacter(ch);
 return sub<Parent(ch)|[ch]>!ch; end intrinsic;

intrinsic GrossenTwist
(psi::GrossenChar,D::List : Hilbert:=false,RequireGenerators:=true) ->
  GrossenChar, GrpHecke
{Given a Grossencharacter, find its twist by a Hecke character
 (of the same modulus as the Grossencharacter) which numerically
 matches the given data (if possible).}
 H:=Parent(psi`hecke); if H`issubgroup then H:=H`supergroup; end if;
 if Hilbert then H:=HilbertCharacterSubgroup(H); end if;
 e:=Exponent(H`AbGrp); Zm:=Integers(e);
 DATA:=[* <d[1],Zm!cyclo_get_power(d[2]/psi(d[1]),e)> : d in D *];
 tw,K:=HeckeCharacter(H,DATA : RequireGenerators:=RequireGenerators);
 return tw*psi,K; end intrinsic; // try/catch?

intrinsic TateTwist(GR::GrossenChar,z::RngIntElt) -> GrossenChar
{Given a Grossencharacter, return its Tate twist by z}
 if z eq 0 then return GR; end if;
 if not GR`field_is_cm then return TateTwist(GR`hecke,-GR`wt+z);
 else return Grossencharacter(GR`hecke,[[u[1]-z,u[2]-z] : u in GR`type]);
 end if; end intrinsic;

intrinsic TateTwist(psi::GrpHeckeElt,z::RngIntElt) -> GrossenChar
 {Given a Hecke character, return its Tate twist by z as a Grossencharacter}
 if IsCMField(psi`Parent`NF) then return
  Grossencharacter(psi,[[-z,-z] : i in [1..Degree(psi`Parent`NF) div 2]]);
 else GR:=New(GrossenChar); GR`hecke:=psi; GR`wt:=-z; GR`field_is_cm:=false;
  return GR; end if; end intrinsic;

////////////////////////////////////////////////////////////////////////

function get_grossen(E) b,cm:=HasComplexMultiplication(E); assert b;
 if cm eq -12 or cm eq -27 then I:=IsogenousCurves(E);
  A:=[e : e in I | u eq -3 where _,u:=HasComplexMultiplication(e)];
  return get_grossen(A[1]); end if;
 if cm eq -16 then I:=IsogenousCurves(E);
  A:=[e : e in I | u eq -4 where _,u:=HasComplexMultiplication(e)];
  return get_grossen(A[1]); end if;
 if cm eq -28 then I:=IsogenousCurves(E);
  A:=[e : e in I | u eq -7 where _,u:=HasComplexMultiplication(e)];
  return get_grossen(A[1]); end if;
 K:=QuadraticField(cm);
 if cm in {-7,-11,-19,-43,-67,-163} then c:=cm eq -11 select "b" else "a";
  T:=EllipticCurve(IntegerToString(cm^2)*c);
  b,tw:=IsQuadraticTwist(E,T); assert b;
  p:=Factorization(cm*Integers(K))[1][1];
  GR:=Grossencharacter(HeckeCharacterGroup(p).0,[[1,0]]);
  psi:=NormInduction(K,KroneckerCharacter(tw));
  psi:=sub<Parent(psi)|[psi]>!psi; // seems to be undone at next step...
  return AssociatedPrimitiveGrossencharacter(psi*GR); end if;
 if cm eq -8 then T:=EllipticCurve("256a");
  b,tw:=IsQuadraticTwist(E,T); assert b;
  p:=Factorization(2*Integers(K))[1][1]; T:=EllipticCurve("256a");
  H:=HeckeCharacterGroup(p^5);
  H:=sub<H|[h : h in Elements(H) | Order(h) eq 2]>;
  G:=[Grossencharacter(h,[[1,0]]) : h in Elements(H)];
  G:=[g : g in G | IsPrimitive(g)];
  GR:=[g : g in G | EulerFactor(g,11 : Integral) eq Polynomial([1,6,11])][1];
  psi:=NormInduction(K,KroneckerCharacter(tw));
  psi:=sub<Parent(psi)|[psi]>!psi; // seems to be undone at next step...
  return AssociatedPrimitiveGrossencharacter(psi*GR); end if;
 if cm eq -3 then c4,c6:=Explode(cInvariants(MinimalModel(E)));
  m:=-54*c6; P:=PrimeFactors(Integers()!m); Exclude(~P,3); Exclude(~P,2);
  K:=QuadraticField(-3); p3:=Factorization(3*Integers(K))[1][1];
  GR:=Grossencharacter(HeckeCharacterGroup(p3^2).0,[[1,0]]);
  // v3:=Valuation(Conductor(E),3); v2:=Valuation(Conductor(E),2);
  v2:=6; v3:=5; // HACK
  I:=&*P*2^(v2 div 2)*p3^(v3-1); RCG,m:=RayClassGroup(I); L:=10;
  CF:=ComplexField(30); zeta6:=CyclotomicField(6).1; B:=[* *];
  while true do Q:=PrimesUpTo(L,K : coprime_to:=I);
   Q:=[q : q in Q | Norm(q) mod 3 eq 1 and Degree(q) eq 1];
   if RCG eq sub<RCG|[p@@m : p in Q]> then break; end if; L:=L+10; end while;
  for p in Q do ap:=-Coefficient(EulerFactor(E,Norm(p)),1);
   ANS:=[zeta6^i : i in [1..6] | Round(2*Real(GR(p)*(CF!zeta6^i))) eq ap];
   assert #ANS eq 1; B:=B cat [*<p,ANS[1]>*]; end for;
  psi,K:=HeckeCharacter(I,<i : i in B>); assert #K eq 1;
  psi:=sub<Parent(psi)|[psi]>!psi; // seems to be undone at next step...
  return AssociatedPrimitiveGrossencharacter(psi*GR); end if;
  // maybe take the Hecke character on the 6^n subgroup ?
 if cm eq -4 then c4,c6:=Explode(cInvariants(MinimalModel(E)));
  m:=-27*c4; P:=PrimeFactors(Integers()!m); Exclude(~P,2);
  K:=QuadraticField(-4); p2:=Factorization(2*Integers(K))[1][1];
  GR:=Grossencharacter(HeckeCharacterGroup(p2^3).0,[[1,0]]);
  I:=&*P*p2^6; RCG,m:=RayClassGroup(I); L:=10;
  CF:=ComplexField(30); zeta4:=CyclotomicField(4).1; B:=[* *];
  while true do Q:=PrimesUpTo(L,K : coprime_to:=I);
   Q:=[q : q in Q | Norm(q) mod 4 eq 1 and Degree(q) eq 1];
   if RCG eq sub<RCG|[p@@m : p in Q]> then break; end if; L:=L+10; end while;
  for p in Q do ap:=-Coefficient(EulerFactor(E,Norm(p)),1);
   ANS:=[zeta4^i : i in [1..4] | Round(2*Real(GR(p)*(CF!zeta4^i))) eq ap];
   assert #ANS eq 1; B:=B cat [*<p,ANS[1]>*]; end for;
  psi,K:=HeckeCharacter(I,<i : i in B>); assert #K eq 1;
  psi:=sub<Parent(psi)|[psi]>!psi; // seems to be undone at next step...
  return AssociatedPrimitiveGrossencharacter(psi*GR); end if; end function;

intrinsic Grossencharacter(E::CrvEll[FldRat]) -> GrossenChar
{Given an elliptic curve over Q with CM by an imaginary quadratic order,
 return the associated Grossencharacter}
 require HasComplexMultiplication(E): "Curve must have complex multiplication";
 GR:=get_grossen(E); P:=PrimesUpTo(100);
 assert &and[EulerFactor(GR,p : Integral) eq EulerFactor(E,p) : p in P];
 return GR; end intrinsic;

intrinsic EllipticCurve(GR::GrossenChar) -> CrvEll
{Given a suitable Grossencharacter over a class number one imaginary
 quadratic field, return the associated elliptic curve over Q}
 K:=GR`hecke`Parent`NF; d:=Discriminant(Integers(K));
 require Degree(K) eq 2 and IsAbsoluteField(K) and Signature(K) eq 0:
 "Base field of Grossencharacter must be imaginary quadratic";
 require d ge -163 and ClassNumber(K) eq 1:
 "Imaginary quadratic field must have class number one";
 GR:=AssociatedPrimitiveGrossencharacter(GR); psi:=CentralCharacter(GR);
 require Order(psi) le 2: "Underlying character must be quadratic";
 L:=LSeries(GR); C:=Conductor(L); P:=PrimeFactors(C);
 require MotivicWeight(L) eq 1: "Weight of Grossencharacter must be [1,0]";
 // require &and[Valuation(C,p) eq 2 : p in P | p ge 5]:
 // "Grossencharacter is not associated to an elliptic curve";
 if not d in {-3,-4} then c:=(d eq -11) select "b" else "a";
  n:=IntegerToString(d^2); if d eq -8 then n:="256"; end if;
  EC:=EllipticCurve(n*c); P:=PrimeFactors(C); Exclude(~P,-d); Exclude(~P,2);
  T:=QuadraticTwist(EC,&*P);
  EF:=[EulerFactor(GR,p : Integral) : p in PrimesUpTo(100)];
  for t in {1,-4,-8,8} do U:=MinimalModel(QuadraticTwist(T,t));
   if EF eq [EulerFactor(U,p) : p in PrimesUpTo(100)] then return U; end if; 
   end for; error "Failed to find the right twist?"; end if;
 if d eq -4 then P:=PrimeFactors(C); Exclude(~P,2); S:=[1,-1,2,-2];
  D:=Decomposition(DirichletRestriction(GR`hecke)/GR`dirich); // divides!
  for p in P do o:=Order([* x : x in D | Norm(Modulus(x)) mod p eq 0 *][1]);
   assert o eq 2 or o eq 4; if o eq 2 then S:=[s*p^2 : s in S]; end if; 
   if o eq 4 then S:=[s*p : s in S] cat [s*p^3 : s in S]; end if; end for;
  EF:=[EulerFactor(GR,p : Integral) : p in PrimesUpTo(100)];
  for s in S do U:=MinimalModel(EllipticCurve([s,0]));
   if EF eq [EulerFactor(U,p) : p in PrimesUpTo(100)] then return U; end if; 
   end for; error "Failed to find the right twist?"; end if;
 if d eq -3 then P:=PrimeFactors(C); Exclude(~P,3); Exclude(~P,2);
  S2:=[1,2,4,8,16,32]; S3:=[1,3,9]; S:=[a*b*c : a in S2,b in S3,c in [-1,1]];
  D:=Decomposition(DirichletRestriction(GR`hecke)/GR`dirich); // divides!
  for p in P do o:=Order([* x : x in D | Norm(Modulus(x)) mod p eq 0 *][1]);
   assert o gt 1 and 6 mod o eq 0; if o eq 2 then S:=[s*p^3 : s in S]; end if; 
   if o eq 3 then S:=[s*p^2 : s in S] cat [s*p^4 : s in S]; end if;
   if o eq 6 then S:=[s*p : s in S] cat [s*p^5 : s in S]; end if; end for;
  EF:=[EulerFactor(GR,p : Integral) : p in PrimesUpTo(100)];
  for s in S do U:=MinimalModel(EllipticCurve([0,s]));
   if EF eq [EulerFactor(U,p) : p in PrimesUpTo(100)] then return U; end if; 
   end for; error "Failed to find the right twist?"; end if; end intrinsic;
