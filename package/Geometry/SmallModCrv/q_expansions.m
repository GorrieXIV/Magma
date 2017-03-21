freeze;
///////////////////////////////////////////////////////////////////
// Functions for q-expansions of the generators of               //
//           Small Modular Curves                                //
//                                                               //
//             mch - 11/2011                                     //
///////////////////////////////////////////////////////////////////

function my_index(str,c,n)
    i := Index(str[n..#str],c);
    if i gt 0 then i +:= n-1; end if;
    return i;
end function;

function statements(str)
// splits the comma separated string of statements into a sequence

    stats := [];
    while true do
	n := Index(str,",");
	if n eq 0 then 
	  Append(~stats,str);
	  break;
	end if;
	Append(~stats,str[1..n-1]);
	str := str[n+1..#str];
    end while;
    return stats;

end function;

function new_var(vars)
  if #vars gt 0 and (Index(vars[#vars],"vt") eq 1) then 
    i := StringToInteger(v[3..#v]) where v is vars[#vars];
    return "vt" cat IntegerToString(i+1);
  end if;
  return "vt1";
end function;

function PowSerDelta(f,d)
// f in Q((q)). Return f(q^d)
  if d eq 1 then return f; end if;
  p := AbsolutePrecision(f);
  v := Valuation(f);
  R := Parent(f);
  pol :=  PolynomialRing(BaseRing(R))!Coefficients(f);
  //pol *:= (Parent(pol).1)^v;
  return ((q^(d*v))*Evaluate(pol,q^d))+O(q^p) where q is R.1;
end function;

function twist_series(f,d)
// f = sum_{n ge 1} a_n q^n in O[[q]]. Returns sum_n a_n*(d/n) q^n
    D := Abs(d);
    seq := [KroneckerSymbol(d,n) : n in [0..D-1]];
    p := AbsolutePrecision(f);
    v := Valuation(f)-1;
    R := Parent(f);
    cs := Coefficients(f);
    cs := [cs[i]*seq[1+((i+v) mod D)] : i in [1..#cs]];
    return (q^(v+1))*(R!cs)+O(q^p) where q is R.1;
end function;

function MyEta(q,prec)
// return q^(-1/24)*eta(z) as a power series in Q[[q]] (q=e^(2*pi*i*z)) up to
// O(q^(prec+1))
    f := Parent(q)!1;
    sgn := 1;
    for n in [1..prec] do
	sgn := -sgn;
	n1 := (n*(3*n-1)) div 2;
	if n1 gt prec then break; end if;
	f +:= sgn*(q^n1);
	n1 +:= n;
	if n1 gt prec then break; end if;
	f +:= sgn*(q^n1);
    end for;
    return f+O(q^(prec+1));	   
end function;

function theta3mod8(A,B,C,R,prec)
    D := 4*A*C-B^2;
    assert D gt 0 and (D mod 8) eq 3;
    QB := BinaryQuadraticForms(-4*D);
    frm1 := QB![A,2*B,4*C];
    frm2 := QB![4*A,4*A+2*B,A+B+C];
    th := ThetaSeries(frm1,2*prec)-ThetaSeries(frm2,2*prec);
    coeffs := [Coefficient(th,2*r-1)/2 : r in [1..prec]];
    return R!coeffs + O((R.1)^prec) ;
end function;

function theta1mod4(A,B,C,R,prec)
    D := 4*A*C-B^2;
    assert D gt 0 and (D mod 16) eq 4;
    if IsEven(A) then u := A; A := C; C := u; end if;
    if IsOdd(C) then C := A+C-B; B := B-2*A; end if; 
    QB := BinaryQuadraticForms(-4*D);
    frm1 := QB![A,2*B,4*C];
    frm2 := QB![4*A,4*A+2*B,A+B+C];
    d := A mod 4;
    th := ThetaSeries(frm1,4*prec+d-1)-ThetaSeries(frm2,4*prec+d-1);
    coeffs := [Coefficient(th,4*r+d)/2 : r in [0..prec-1]];
    return (R!coeffs + O((R.1)^prec)),d ;
end function;

function theta2mod8(A,B,C,R,prec)
    D := 4*A*C-B^2;
    assert D gt 0 and (D mod 16) eq 4;
    if IsEven(A) then u := A; A := C; C := u; end if;
    if IsOdd(C) then C := A+C-B; B := B-2*A; end if; 
    QB := BinaryQuadraticForms(-D);
    QB1 := BinaryQuadraticForms(-4*D);
    frm1 := QB![A,B,C];
    frm2 := QB1![4*A,2*B,C];
    d := A mod 4;
    th := ThetaSeries(frm1,4*prec+d-1)-ThetaSeries(frm2,4*prec+d-1);
    coeffs := [Coefficient(th,4*r+d)/2 : r in [0..prec-1]];
    return (R!coeffs + O((R.1)^prec)),d ;
end function;

function thetaquat(N,R,prec)
    fact := Factorisation(N);
    assert IsOdd(#fact) and &and[f[2] eq 1 : f in fact];
    ps := [f[1]: f in fact];
    A := QuaternionAlgebra(N);
    ordA := MaximalOrder(A);
    mat := Matrix(Integers(),4,4,[Trace(b)*Trace(c)-Trace(b*c): 
		b in B, c in B]) where B is Basis(ordA);
    L := LatticeWithGram(mat);
    th := ThetaSeries(L,2*prec);
    return R![Coefficient(th,2*r) : r in [0..prec]] + O(R.1^(prec+1));
end function;

function Eisensteinp(k,p,R,prec)
    assert IsEven(k);
    eis := Eisenstein(k,R.1+O(R.1^(prec+1)));
    return -eis+p^(k div 2)*PowSerDelta(eis,p);
end function;

function eval_eta_prod(e,R,r)
// e is a string giving the expression for an eta product. Compute this product
// in R=Q[[q]] up to O(q^{r+1}).

    pairs := [];
    while true do
      i := Index(e,"<");
      if i eq 0 then break; end if;
      j := Index(e," ");
      k := Index(e,">");
      Append(~pairs,<StringToInteger(e[i+1..j-1]),StringToInteger(e[j+1..k-1])>);
      e := e[k+1..#e];     
    end while;
    n := &+[p[1]*p[2] : p in pairs];
    boo,n := IsDivisibleBy(n,24);
    assert boo;
    eta := MyEta(R.1,Max(r-n,0));
    prod := &*[PowSerDelta(eta,p[1])^p[2] : p in pairs];
    if n ne 0 then prod := (R.1^n)*prod; end if;
    return prod;

end function;

function eval_theta(e,R,r)
// e is the string defining a theta function th_Q(mz) where Q is a binary quad form
//  and th is plain, 1 mod 4, 2 mod 8 or 3 mod 8 type or Q comes from a quaternion
//  algebra. Compute the series expansion in R=Q[[q]] to precision O(q^{r+1})

    j := Index(e,"}"); d := 1;
    if j lt #e then
	d := StringToInteger(e[j+2..#e-1]);
    end if;

    if e[3] eq "Q" then
	typ := 4;
	N := StringToInteger(e[5..j-1]);
	val := thetaquat(N,R,r);
    else 
	typ := StringToInteger(e[3]);
	A,B,C := Explode(StringToIntegerSequence(e[5..j-1]));
	case typ:
	  when 0: val := R!ThetaSeries(BinaryQuadraticForms(B^2-4*A*C)![A,B,C],r);
	  when 1: val := theta1mod4(A,B,C,R,r);
	  when 2: val := theta2mod8(A,B,C,R,r);
	  when 3: val := theta3mod8(A,B,C,R,r);
	end case
    end if;

    if d gt 1 then val := PowSerDelta(val,d); end if;
    return val;

end function;

function eval_E2(e,R,r)
// e is the string defining E2p(dz) where E2p(z) := (pE2(pz)-E2(z))/m where m is (24,p-1).
//  Computes and returns the series expansion in R=Q[[q]] to precision O(q^{r+1})

    j := Index(e,"}"); d := 1;
    p := StringToInteger(e[3..j-1]);
    if j lt #e then
	d := StringToInteger(e[j+2..#e-1]);
    end if;
    val := Eisensteinp(2,p,R,r);
    m := GCD(p-1,24);
    val := val/m; 
    if d gt 1 then val := PowSerDelta(val,d); end if;
    return val;

end function;

function eval_elliptic(e,R,r)
// e is the string defining f(z) the wt 2 newform associated to an elliptic curve E/Q.
//  Computes and returns the series expansion in R=Q[[q]] to precision O(q^{r+1})

    as := StringToIntegerSequence(e[3..#e-1]);
    E := EllipticCurve(as);
    f := ModularForm(E);
    return qExpansion(f,r+1);

end function;

function tokenise(stat)
// split statement stat into tokens

   toks := [];
   //n := 1; N := #stat;
   while #stat gt 0 do
     c := stat[1];
     if c in "+-*^/q" then
	m := 1;
     elif c eq "e" then // eta product
	m := Index(stat,"}");
     elif (c eq "t" and (#stat gt 1) and (stat[2] eq "h")) //theta function
	    or (c eq "E") //wt 2 Eisenstein series
	    or (c eq "f") //wt 2 cusp form from an elliptic curve
		then
	m := Index(stat,"}");
	if (m lt #stat) and (stat[m+1] eq "[") then
	  m := Index(stat,"]");
	end if;
     elif c eq "<" then //twist by a quadratic char
	m := Index(stat,">");
     elif (c ge "0") and (c le "9") then //integer
	m := 2;
	while (m le #stat) and (stat[m] in "0123456789") do
	  m +:= 1;
	end while;
	m -:= 1;
     else //variable or Dvariable
	m := 2;
	while (m le #stat) and not(stat[m] in "+-*^/<[") do m +:= 1; end while;
	if (m le #stat) and (stat[m] eq "[") then
	  m := Index(stat,"]");
	else
	  m -:= 1;
	end if;
     end if; 
     Append(~toks,stat[1..m]);
     stat := stat[m+1..#stat];
   end while;
   return toks;

end function;

function compute_val(stat,vars,vals,R,r)
// compute the q-expansion in Laurent Series Ring R given by evaluating statement stat.
// vars are a list of variables already computed with values in vals. r is the precision
// to compute the value to (ie result to O(q^r))

   //expand brackets and replace with new variables
   vrs := vars; vls := vals;
   while true do
     n :=  Index(stat,"(");
     if n ne 0 then
	m := Index(stat,")");
	ns := 0; v := my_index(stat,"(",n+1);
	while (v gt 0) and (v lt m) do
	  ns +:= 1;
	  v := my_index(stat,"(",v+1);
	end while;
	for i in [1..ns] do
	  m := Index(stat[m+1..#stat],")")+m;
	end for;
	val := compute_val(stat[n+1..m-1],vrs,vls,R,r);
	Append(~vrs,new_var(vrs));
	Append(~vls,val);
	stat := stat[1..n-1] cat vrs[#vrs] cat stat[m+1..#stat];
      else
	break;
      end if;
   end while;
   //tokenise statement
   toks := tokenise(stat);
   //evaluate toks
   vs := [**];
   for tok in toks do
     if tok in {@ "+","-","*","^","/" @} then
	Append(~vs,tok);
     else
	c := tok[1];
	if c eq "e" then
	  val := eval_eta_prod(tok,R,r);
	elif c eq "q" then
	  val := R.1;
	elif c eq "t" and (#tok gt 1) and (tok[2] eq "h") then
	  val := eval_theta(tok,R,r);
	elif c eq "E" then
	  val := eval_E2(tok,R,r);
	elif c eq "f" then
	  val := eval_elliptic(tok,R,r);
	elif c eq "<" then
	  val := [StringToInteger(tok[2..#tok-1])];
	elif (c ge "0") and (c le "9") then
	  val := StringToInteger(tok);
	else
	  j:= #tok; d:= 1;
	  if c eq "D" then 
	    i := 2;
	  else
	    i := 1;
	    m := Index(tok,"[");
	    if m ne 0 then
		j := m-1;
		m := Index(tok,"]");
		d := StringToInteger(tok[j+2..m-1]);
	    end if;
	  end if;
	  i := Index(vrs,tok[i..j]);
	  assert i gt 0;
	  val := vls[i];
	  if c eq "D" then 
	    val := (R.1)*Derivative(val);
	  elif d gt 1 then
	    val := PowSerDelta(val,d);
	  end if;
	end if;
	Append(~vs,val);
     end if;
   end for;
   // compute total value
      //leading -?
   if vs[1] cmpeq "-" then
      vs[2] := -vs[2];
      Remove(~vs,1);
   end if;
      //first compute any quadratic twists
   for i := #vs to 1 by -1 do
      if Type(vs[i]) eq SeqEnum then //twist by quad char
	vs[i-1] := twist_series(vs[i-1],vs[i][1]);
	Remove(~vs,i);
      end if;
   end for;
     //do powers
   js := Reverse([i : i in [1..#vs] | vs[i] cmpeq "^"]);
   for i in js do
	vs[i-1] := vs[i-1]^(vs[i+1]);
	Remove(~vs,i+1); Remove(~vs,i);
   end for;
     //do multiplications
   js := Reverse([i : i in [1..#vs] | vs[i] cmpeq "*"]);
   for i in js do
	vs[i-1] := vs[i-1]*vs[i+1];
	Remove(~vs,i+1); Remove(~vs,i);
   end for;
     //do divisions
   js := Reverse([i : i in [1..#vs] | vs[i] cmpeq "/"]);
   for i in js do
	vs[i-1] := vs[i-1]/vs[i+1];
	Remove(~vs,i+1); Remove(~vs,i);
   end for;
     //rest are + and - terms
   n := #vs; i := 2;
   val := vs[1];
   while i lt n do
     if vs[i] cmpeq "+" then
	val := val+vs[i+1];
     elif vs[i] cmpeq "-" then
	val := val-vs[i+1];
     else
	error "Syntax error evaluating q-expansion expression.";
     end if;
     i +:= 2;
   end while;
   return val;

end function;

function build_q_expansions(str,R,r)

    stats := statements(str);
    //R<q> := LaurentSeriesRing(Q);
    vars := [];
    vals := [R|];
    ret_vals := [];
    for stat in stats do
	n := Index(stat,"=");
	if n eq 0 then
	  sps := [1,Index(stat," ")];
	  while true do
	    i := sps[#sps];
	    j := Index(stat[i+1..#stat]," ");
	    if j eq 0 then break; end if;
	    Append(~sps,j+i);
	  end while;
	  Append(~sps,#stat);
	  es := [stat[sps[i]+1..sps[i+1]-1] : i in [1..#sps-1]];
		//[stat[2..i-1],stat[i+1..j-1],stat[j+1..#stat-1]];
	  ret_vals := [compute_val(e,vars,vals,R,r) : e in es];
	else
	  var := stat[1..n-1];
	  val := compute_val(stat[n+1..#stat],vars,vals,R,r);
	  Append(~vars,var);
	  Append(~vals,val);
	end if;
    end for;

    if #ret_vals gt 0 then return ret_vals; end if;
    i := Index(vars,"x");
    vx := vals[i];
    i := Index(vars,"y");
    if i eq 0 then
	return [vx];
    else
	return [vx,vals[i]];
    end if;

end function;

intrinsic qExpansionsOfGenerators(N::RngIntElt, R::RngSerLaur, r::RngIntElt) -> SeqEnum
{ Returns the q-expansions of the coordinate generators of the small modular curve database model of X0(N)
  to precision r in R, a Laurent series ring over Q }

    require N gt 0: "N should be a positive integer";
    require BaseRing(R) cmpeq Rationals():
     "Secong argument should be a Laurent series ring over the rationals Q";
    require r ge 0: 
     "Third argument should be non-negative";
    try
      X0Nrec := Create_SmallCrvMod_Structure(N);
    catch e
      error e`Object;
    end try;
    str := X0Nrec`qexps;

    gs := build_q_expansions(str,R,r+10);
    gs := [g+O(q^(r+1)) : g in gs] where q is R.1;
    return gs;

end intrinsic;

intrinsic qExpansionExpressions(N::RngIntElt)
{ Print out the sequence of expressions to generate the q-expansions of the modular functions/forms
  represented by the coordinate functions of the small modular curve database model of X0(N). For the format
  of the output, see the handbook documentation. }

    require N gt 0: "N should be a positive integer";
    try
      X0Nrec := Create_SmallCrvMod_Structure(N);
    catch e
      error e`Object;
    end try;
    str := X0Nrec`qexps;

    stats := statements(str);
    if Index(stats[#stats],"=") ne 0 then
	if N in [1..10] cat [12,13,16,18,25] then
	  Append(~stats,"[x,1]");
	else
	  Append(~stats,"[x,y,1]");
	end if;
    else
	//replace spaces by commas in the final stat
	stat := stats[#stats];
	spl := Split(stat," ");
	stat1 := &cat[s cat "," : s in spl];
	Prune(~stat1);
	stats[#stats] := stat1;
    end if;
    for s in stats do
	s;
    end for;
    return;

end intrinsic;
