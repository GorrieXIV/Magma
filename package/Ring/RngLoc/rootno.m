
freeze;

// root number of an extension K/Qp, from 3.3 of Jones and Roberts

Z:=Integers();

function eps2_factor(d) C<zeta_4>:=CyclotomicField(4);
 v:=Valuation(d); r:=d/2^Valuation(d);
 cl:=[IsSquare(r),IsSquare(-3*r),IsSquare(-r)];
 if cl[1] then return C!1; end if;
 if cl[2] then return IsEven(v) select C!1 else C!-1; end if;
 if cl[3] then return C.1; end if;
 return IsEven(v) select C.1 else -C.1; end function;

function eps_factor(d,p) C<zeta_4>:=CyclotomicField(4);
 if p eq 2 then return eps2_factor(d); end if;
 v:=Valuation(d); if IsEven(v) then return C!1; end if;
 sq:=IsSquare(d/p^Valuation(d));
 if p mod 4 eq 1 then return sq select C!1 else C!-1; end if;
 return sq select -C.1 else C.1; end function;

function trace_matrix(L)
 B:=AbsoluteBasis(L); d:=AbsoluteDegree(L); Qp:=PrimeField(L);
 return Matrix(d,d,[Trace(B[i]*B[j],Qp) : i, j in [1..d]]); end function;

function root_number_Qp(L) p:=Prime(L); d:=Discriminant(L,PrimeField(L));
 hw:=WittInvariant(ChangeRing(trace_matrix(L),Z),p); eps:=eps_factor(d,p);
 hs:=HilbertSymbol(2,Z!d,p); return hw*hs*eps; end function;

intrinsic RootNumber(K::FldPad) -> FldCycElt
{Given a p-adic field, return the relative root number in Q<zeta_4>}
 if Degree(K) eq AbsoluteDegree(K) then return root_number_Qp(K); end if;
 return root_number_Qp(K)/RootNumber(BaseRing(K))^Degree(K); end intrinsic;

intrinsic AbsoluteRootNumber(K::FldPad) -> FldCycElt
{Given a p-adic field, return the absolute root number in Q<zeta_4>}
 return root_number_Qp(K); end intrinsic;
