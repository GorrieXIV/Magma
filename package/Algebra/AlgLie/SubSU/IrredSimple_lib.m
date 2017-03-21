freeze;

/*
Algorithms to find irreducible simple subalgebras of su(N)
Author: Robert Zeier, 17 May 2011
*/

declare verbose SubSU, 1;

string2tuple:=func<a|<a[1],StringToInteger(a[2..#a])>>;
tuple2string:=func<a|a[1] cat IntegerToString(a[2])>;

function dim_poly_fact(RD);
  pos_roots:=PositiveRoots(RD:Basis:="Weight");
  fund_weights:=Rows(FundamentalWeights(RD:Basis:="Weight"));
  halfsum:=&+fund_weights;
  cox_form:=CoxeterForm(RD:Basis:="Weight");
  ring:=PolynomialRing(Rationals(),#fund_weights);
  inv_prod:=func<x,y|InnerProduct(x*cox_form,y)>;

  pol_list:=[];
  for i in pos_roots do
    Append(~pol_list,1+(&+[Name(ring,j)*inv_prod(fund_weights[j],i):j in [1..Rank(ring)]])/inv_prod(halfsum,i));
  end for;

  return pol_list;
end function;

function ReprDimFuncTest(N);
  RD:=RootDatum(N:Isogeny:="SC");
  v:=dim_poly_fact(RD);
  return func<a|Integers()!(&*[Evaluate(i,a):i in v])>;
end function;

function ReprDimFuncList_Xn(X,n); 
  case X:
    when "A":
      P:=PolynomialRing(Rationals(),n);
      list:=[1+(&+[P|P.k:k in [i..(j-1)]])/(j-i):i in [1..j-1], j in [1..n+1]];
    when "B":
      P:=PolynomialRing(Rationals(),n);
      list:=[1+(&+[P|P.k:k in [i..(j-1)]])/(j-i):i in [1..j-1], j in [1..n]] cat [1+((&+[P|P.k:k in [i..(j-1)]])+2*(&+[P|P.k:k in [j..(n-1)]])+P.n)/(2*n+1-i-j):i in [1..j-1], j in [1..n]] cat [1+(2*(&+[P|P.k:k in [i..(n-1)]])+P.n)/(2*n+1-2*i):i in [1..n]];
    when "C":
      P:=PolynomialRing(Rationals(),n);
      list:=[1+(&+[P|P.k:k in [i..(j-1)]])/(j-i):i in [1..j-1],j in [1..n]] cat [1+((&+[P|P.k:k in [i..(j-1)]])+2*(&+[P|P.k:k in [j..n]]))/(2*n+2-i-j):i in [1..j-1],j in [1..n]] cat [1+((&+[P|P.k:k in [i..n]]))/(n+1-i):i in [1..n]];
    when "D":
      P:=PolynomialRing(Rationals(),n);
      list:=[1+(&+[P|P.k:k in [i..(j-1)]])/(j-i):i in [1..j-1],j in [1..n]] cat [1+((&+[P|P.k:k in [i..j-1]])+2*(&+[P|P.k:k in [j..(n-2)]])+P.(n-1)+P.n)/(2*n-i-j):i in [1..j-1], j in [1..n-1]] cat [1+((&+[P|P.k:k in [i..n-2]])+P.n)/(n-i):i in [1..n-1]];
    when "E":
      case n:
        when 6:
          P:=PolynomialRing(Rationals(),n);
          list:=
            [
            P.1 + 1,
            P.2 + 1,
            P.3 + 1,
            P.4 + 1,
            P.5 + 1,
            P.6 + 1,
            1/2*P.1 + 1/2*P.3 + 1,
            1/2*P.2 + 1/2*P.4 + 1,
            1/2*P.3 + 1/2*P.4 + 1,
            1/2*P.4 + 1/2*P.5 + 1,
            1/2*P.5 + 1/2*P.6 + 1,
            1/3*P.1 + 1/3*P.3 + 1/3*P.4 + 1,
            1/3*P.2 + 1/3*P.3 + 1/3*P.4 + 1,
            1/3*P.2 + 1/3*P.4 + 1/3*P.5 + 1,
            1/3*P.3 + 1/3*P.4 + 1/3*P.5 + 1,
            1/3*P.4 + 1/3*P.5 + 1/3*P.6 + 1,
            1/4*P.1 + 1/4*P.2 + 1/4*P.3 + 1/4*P.4 + 1,
            1/4*P.1 + 1/4*P.3 + 1/4*P.4 + 1/4*P.5 + 1,
            1/4*P.2 + 1/4*P.3 + 1/4*P.4 + 1/4*P.5 + 1,
            1/4*P.2 + 1/4*P.4 + 1/4*P.5 + 1/4*P.6 + 1,
            1/4*P.3 + 1/4*P.4 + 1/4*P.5 + 1/4*P.6 + 1,
            1/5*P.1 + 1/5*P.2 + 1/5*P.3 + 1/5*P.4 + 1/5*P.5 + 1,
            1/5*P.1 + 1/5*P.3 + 1/5*P.4 + 1/5*P.5 + 1/5*P.6 + 1,
            1/5*P.2 + 1/5*P.3 + 2/5*P.4 + 1/5*P.5 + 1,
            1/5*P.2 + 1/5*P.3 + 1/5*P.4 + 1/5*P.5 + 1/5*P.6 + 1,
            1/6*P.1 + 1/6*P.2 + 1/6*P.3 + 1/3*P.4 + 1/6*P.5 + 1,
            1/6*P.1 + 1/6*P.2 + 1/6*P.3 + 1/6*P.4 + 1/6*P.5 + 1/6*P.6 + 1,
            1/6*P.2 + 1/6*P.3 + 1/3*P.4 + 1/6*P.5 + 1/6*P.6 + 1,
            1/7*P.1 + 1/7*P.2 + 2/7*P.3 + 2/7*P.4 + 1/7*P.5 + 1,
            1/7*P.1 + 1/7*P.2 + 1/7*P.3 + 2/7*P.4 + 1/7*P.5 + 1/7*P.6 + 1,
            1/7*P.2 + 1/7*P.3 + 2/7*P.4 + 2/7*P.5 + 1/7*P.6 + 1,
            1/8*P.1 + 1/8*P.2 + 1/4*P.3 + 1/4*P.4 + 1/8*P.5 + 1/8*P.6 + 1,
            1/8*P.1 + 1/8*P.2 + 1/8*P.3 + 1/4*P.4 + 1/4*P.5 + 1/8*P.6 + 1,
            1/9*P.1 + 1/9*P.2 + 2/9*P.3 + 2/9*P.4 + 2/9*P.5 + 1/9*P.6 + 1,
            1/10*P.1 + 1/10*P.2 + 1/5*P.3 + 3/10*P.4 + 1/5*P.5 + 1/10*P.6 + 1,
            1/11*P.1 + 2/11*P.2 + 2/11*P.3 + 3/11*P.4 + 2/11*P.5 + 1/11*P.6 + 1
            ];
        when 7:
          P:=PolynomialRing(Rationals(),n);
          list:=
            [
            P.1 + 1,
            P.2 + 1,
            P.3 + 1,
            P.4 + 1,
            P.5 + 1,
            P.6 + 1,
            P.7 + 1,
            1/2*P.1 + 1/2*P.3 + 1,
            1/2*P.2 + 1/2*P.4 + 1,
            1/2*P.3 + 1/2*P.4 + 1,
            1/2*P.4 + 1/2*P.5 + 1,
            1/2*P.5 + 1/2*P.6 + 1,
            1/2*P.6 + 1/2*P.7 + 1,
            1/3*P.1 + 1/3*P.3 + 1/3*P.4 + 1,
            1/3*P.2 + 1/3*P.3 + 1/3*P.4 + 1,
            1/3*P.2 + 1/3*P.4 + 1/3*P.5 + 1,
            1/3*P.3 + 1/3*P.4 + 1/3*P.5 + 1,
            1/3*P.4 + 1/3*P.5 + 1/3*P.6 + 1,
            1/3*P.5 + 1/3*P.6 + 1/3*P.7 + 1,
            1/4*P.1 + 1/4*P.2 + 1/4*P.3 + 1/4*P.4 + 1,
            1/4*P.1 + 1/4*P.3 + 1/4*P.4 + 1/4*P.5 + 1,
            1/4*P.2 + 1/4*P.3 + 1/4*P.4 + 1/4*P.5 + 1,
            1/4*P.2 + 1/4*P.4 + 1/4*P.5 + 1/4*P.6 + 1,
            1/4*P.3 + 1/4*P.4 + 1/4*P.5 + 1/4*P.6 + 1,
            1/4*P.4 + 1/4*P.5 + 1/4*P.6 + 1/4*P.7 + 1,
            1/5*P.1 + 1/5*P.2 + 1/5*P.3 + 1/5*P.4 + 1/5*P.5 + 1,
            1/5*P.1 + 1/5*P.3 + 1/5*P.4 + 1/5*P.5 + 1/5*P.6 + 1,
            1/5*P.2 + 1/5*P.3 + 2/5*P.4 + 1/5*P.5 + 1,
            1/5*P.2 + 1/5*P.3 + 1/5*P.4 + 1/5*P.5 + 1/5*P.6 + 1,
            1/5*P.2 + 1/5*P.4 + 1/5*P.5 + 1/5*P.6 + 1/5*P.7 + 1,
            1/5*P.3 + 1/5*P.4 + 1/5*P.5 + 1/5*P.6 + 1/5*P.7 + 1,
            1/6*P.1 + 1/6*P.2 + 1/6*P.3 + 1/3*P.4 + 1/6*P.5 + 1,
            1/6*P.1 + 1/6*P.2 + 1/6*P.3 + 1/6*P.4 + 1/6*P.5 + 1/6*P.6 + 1,
            1/6*P.1 + 1/6*P.3 + 1/6*P.4 + 1/6*P.5 + 1/6*P.6 + 1/6*P.7 + 1,
            1/6*P.2 + 1/6*P.3 + 1/3*P.4 + 1/6*P.5 + 1/6*P.6 + 1,
            1/6*P.2 + 1/6*P.3 + 1/6*P.4 + 1/6*P.5 + 1/6*P.6 + 1/6*P.7 + 1,
            1/7*P.1 + 1/7*P.2 + 2/7*P.3 + 2/7*P.4 + 1/7*P.5 + 1,
            1/7*P.1 + 1/7*P.2 + 1/7*P.3 + 2/7*P.4 + 1/7*P.5 + 1/7*P.6 + 1,
            1/7*P.1 + 1/7*P.2 + 1/7*P.3 + 1/7*P.4 + 1/7*P.5 + 1/7*P.6 + 1/7*P.7 + 1,
            1/7*P.2 + 1/7*P.3 + 2/7*P.4 + 2/7*P.5 + 1/7*P.6 + 1,
            1/7*P.2 + 1/7*P.3 + 2/7*P.4 + 1/7*P.5 + 1/7*P.6 + 1/7*P.7 + 1,
            1/8*P.1 + 1/8*P.2 + 1/4*P.3 + 1/4*P.4 + 1/8*P.5 + 1/8*P.6 + 1,
            1/8*P.1 + 1/8*P.2 + 1/8*P.3 + 1/4*P.4 + 1/4*P.5 + 1/8*P.6 + 1,
            1/8*P.1 + 1/8*P.2 + 1/8*P.3 + 1/4*P.4 + 1/8*P.5 + 1/8*P.6 + 1/8*P.7 + 1,
            1/8*P.2 + 1/8*P.3 + 1/4*P.4 + 1/4*P.5 + 1/8*P.6 + 1/8*P.7 + 1,
            1/9*P.1 + 1/9*P.2 + 2/9*P.3 + 2/9*P.4 + 2/9*P.5 + 1/9*P.6 + 1,
            1/9*P.1 + 1/9*P.2 + 2/9*P.3 + 2/9*P.4 + 1/9*P.5 + 1/9*P.6 + 1/9*P.7 + 1,
            1/9*P.1 + 1/9*P.2 + 1/9*P.3 + 2/9*P.4 + 2/9*P.5 + 1/9*P.6 + 1/9*P.7 + 1,
            1/9*P.2 + 1/9*P.3 + 2/9*P.4 + 2/9*P.5 + 2/9*P.6 + 1/9*P.7 + 1,
            1/10*P.1 + 1/10*P.2 + 1/5*P.3 + 3/10*P.4 + 1/5*P.5 + 1/10*P.6 + 1,
            1/10*P.1 + 1/10*P.2 + 1/5*P.3 + 1/5*P.4 + 1/5*P.5 + 1/10*P.6 + 1/10*P.7 + 1,
            1/10*P.1 + 1/10*P.2 + 1/10*P.3 + 1/5*P.4 + 1/5*P.5 + 1/5*P.6 + 1/10*P.7 + 1,
            1/11*P.1 + 2/11*P.2 + 2/11*P.3 + 3/11*P.4 + 2/11*P.5 + 1/11*P.6 + 1,
            1/11*P.1 + 1/11*P.2 + 2/11*P.3 + 3/11*P.4 + 2/11*P.5 + 1/11*P.6 + 1/11*P.7 + 1,
            1/11*P.1 + 1/11*P.2 + 2/11*P.3 + 2/11*P.4 + 2/11*P.5 + 2/11*P.6 + 1/11*P.7 + 1,
            1/12*P.1 + 1/6*P.2 + 1/6*P.3 + 1/4*P.4 + 1/6*P.5 + 1/12*P.6 + 1/12*P.7 + 1,
            1/12*P.1 + 1/12*P.2 + 1/6*P.3 + 1/4*P.4 + 1/6*P.5 + 1/6*P.6 + 1/12*P.7 + 1,
            1/13*P.1 + 2/13*P.2 + 2/13*P.3 + 3/13*P.4 + 2/13*P.5 + 2/13*P.6 + 1/13*P.7 + 1,
            1/13*P.1 + 1/13*P.2 + 2/13*P.3 + 3/13*P.4 + 3/13*P.5 + 2/13*P.6 + 1/13*P.7 + 1,
            1/14*P.1 + 1/7*P.2 + 1/7*P.3 + 3/14*P.4 + 3/14*P.5 + 1/7*P.6 + 1/14*P.7 + 1,
            1/15*P.1 + 2/15*P.2 + 2/15*P.3 + 4/15*P.4 + 1/5*P.5 + 2/15*P.6 + 1/15*P.7 + 1,
            1/16*P.1 + 1/8*P.2 + 3/16*P.3 + 1/4*P.4 + 3/16*P.5 + 1/8*P.6 + 1/16*P.7 + 1,
            2/17*P.1 + 2/17*P.2 + 3/17*P.3 + 4/17*P.4 + 3/17*P.5 + 2/17*P.6 + 1/17*P.7 + 1
            ];
        when 8:
          P:=PolynomialRing(Rationals(),n);
          list:=
            [
            P.1 + 1,
            P.2 + 1,
            P.3 + 1,
            P.4 + 1,
            P.5 + 1,
            P.6 + 1,
            P.7 + 1,
            P.8 + 1,
            1/2*P.1 + 1/2*P.3 + 1,
            1/2*P.2 + 1/2*P.4 + 1,
            1/2*P.3 + 1/2*P.4 + 1,
            1/2*P.4 + 1/2*P.5 + 1,
            1/2*P.5 + 1/2*P.6 + 1,
            1/2*P.6 + 1/2*P.7 + 1,
            1/2*P.7 + 1/2*P.8 + 1,
            1/3*P.1 + 1/3*P.3 + 1/3*P.4 + 1,
            1/3*P.2 + 1/3*P.3 + 1/3*P.4 + 1,
            1/3*P.2 + 1/3*P.4 + 1/3*P.5 + 1,
            1/3*P.3 + 1/3*P.4 + 1/3*P.5 + 1,
            1/3*P.4 + 1/3*P.5 + 1/3*P.6 + 1,
            1/3*P.5 + 1/3*P.6 + 1/3*P.7 + 1,
            1/3*P.6 + 1/3*P.7 + 1/3*P.8 + 1,
            1/4*P.1 + 1/4*P.2 + 1/4*P.3 + 1/4*P.4 + 1,
            1/4*P.1 + 1/4*P.3 + 1/4*P.4 + 1/4*P.5 + 1,
            1/4*P.2 + 1/4*P.3 + 1/4*P.4 + 1/4*P.5 + 1,
            1/4*P.2 + 1/4*P.4 + 1/4*P.5 + 1/4*P.6 + 1,
            1/4*P.3 + 1/4*P.4 + 1/4*P.5 + 1/4*P.6 + 1,
            1/4*P.4 + 1/4*P.5 + 1/4*P.6 + 1/4*P.7 + 1,
            1/4*P.5 + 1/4*P.6 + 1/4*P.7 + 1/4*P.8 + 1,
            1/5*P.1 + 1/5*P.2 + 1/5*P.3 + 1/5*P.4 + 1/5*P.5 + 1,
            1/5*P.1 + 1/5*P.3 + 1/5*P.4 + 1/5*P.5 + 1/5*P.6 + 1,
            1/5*P.2 + 1/5*P.3 + 2/5*P.4 + 1/5*P.5 + 1,
            1/5*P.2 + 1/5*P.3 + 1/5*P.4 + 1/5*P.5 + 1/5*P.6 + 1,
            1/5*P.2 + 1/5*P.4 + 1/5*P.5 + 1/5*P.6 + 1/5*P.7 + 1,
            1/5*P.3 + 1/5*P.4 + 1/5*P.5 + 1/5*P.6 + 1/5*P.7 + 1,
            1/5*P.4 + 1/5*P.5 + 1/5*P.6 + 1/5*P.7 + 1/5*P.8 + 1,
            1/6*P.1 + 1/6*P.2 + 1/6*P.3 + 1/3*P.4 + 1/6*P.5 + 1,
            1/6*P.1 + 1/6*P.2 + 1/6*P.3 + 1/6*P.4 + 1/6*P.5 + 1/6*P.6 + 1,
            1/6*P.1 + 1/6*P.3 + 1/6*P.4 + 1/6*P.5 + 1/6*P.6 + 1/6*P.7 + 1,
            1/6*P.2 + 1/6*P.3 + 1/3*P.4 + 1/6*P.5 + 1/6*P.6 + 1,
            1/6*P.2 + 1/6*P.3 + 1/6*P.4 + 1/6*P.5 + 
            1/6*P.6 + 1/6*P.7 + 1,
            1/6*P.2 + 1/6*P.4 + 1/6*P.5 + 1/6*P.6 + 1/6*P.7 + 1/6*P.8 + 1,
            1/6*P.3 + 1/6*P.4 + 1/6*P.5 + 1/6*P.6 + 1/6*P.7 + 1/6*P.8 + 1,
            1/7*P.1 + 1/7*P.2 + 2/7*P.3 + 2/7*P.4 + 1/7*P.5 + 1,
            1/7*P.1 + 1/7*P.2 + 1/7*P.3 + 2/7*P.4 + 1/7*P.5 + 1/7*P.6 + 1,
            1/7*P.1 + 1/7*P.2 + 1/7*P.3 + 1/7*P.4 + 1/7*P.5 + 1/7*P.6 + 1/7*P.7 + 1,
            1/7*P.1 + 1/7*P.3 + 1/7*P.4 + 1/7*P.5 + 1/7*P.6 + 1/7*P.7 + 1/7*P.8 + 1,
            1/7*P.2 + 1/7*P.3 + 2/7*P.4 + 2/7*P.5 + 1/7*P.6 + 1,
            1/7*P.2 + 1/7*P.3 + 2/7*P.4 + 1/7*P.5 + 1/7*P.6 + 1/7*P.7 + 1,
            1/7*P.2 + 1/7*P.3 + 1/7*P.4 + 1/7*P.5 + 1/7*P.6 + 1/7*P.7 + 1/7*P.8 + 1,
            1/8*P.1 + 1/8*P.2 + 1/4*P.3 + 1/4*P.4 + 1/8*P.5 + 1/8*P.6 + 1,
            1/8*P.1 + 1/8*P.2 + 1/8*P.3 + 1/4*P.4 + 1/4*P.5 + 1/8*P.6 + 1,
            1/8*P.1 + 1/8*P.2 + 1/8*P.3 + 1/4*P.4 + 1/8*P.5 + 1/8*P.6 + 1/8*P.7 + 1,
            1/8*P.1 + 1/8*P.2 + 1/8*P.3 + 1/8*P.4 + 1/8*P.5 + 1/8*P.6 + 1/8*P.7 + 1/8*P.8 + 1,
            1/8*P.2 + 1/8*P.3 + 1/4*P.4 + 1/4*P.5 + 1/8*P.6 + 1/8*P.7 + 1,
            1/8*P.2 + 1/8*P.3 + 1/4*P.4 + 1/8*P.5 + 1/8*P.6 + 1/8*P.7 + 1/8*P.8 + 1,
            1/9*P.1 + 1/9*P.2 + 2/9*P.3 + 2/9*P.4 + 2/9*P.5 + 1/9*P.6 + 1,
            1/9*P.1 + 1/9*P.2 + 2/9*P.3 + 2/9*P.4 + 1/9*P.5 + 1/9*P.6 + 1/9*P.7 + 1,
            1/9*P.1 + 1/9*P.2 + 1/9*P.3 + 2/9*P.4 + 2/9*P.5 + 1/9*P.6 + 1/9*P.7 + 1,
            1/9*P.1 + 1/9*P.2 + 1/9*P.3 + 2/9*P.4 + 1/9*P.5 + 1/9*P.6 + 1/9*P.7 + 1/9*P.8 + 1,
            1/9*P.2 + 1/9*P.3 + 2/9*P.4 + 2/9*P.5 + 2/9*P.6 + 1/9*P.7 + 1,
            1/9*P.2 + 1/9*P.3 + 2/9*P.4 + 2/9*P.5 + 1/9*P.6 + 1/9*P.7 + 1/9*P.8 + 1,
            1/10*P.1 + 1/10*P.2 + 1/5*P.3 + 3/10*P.4 + 1/5*P.5 + 1/10*P.6 + 1,
            1/10*P.1 + 1/10*P.2 + 1/5*P.3 + 1/5*P.4 + 1/5*P.5 + 1/10*P.6 + 1/10*P.7 + 1,
            1/10*P.1 + 1/10*P.2 + 1/5*P.3 + 1/5*P.4 + 1/10*P.5 + 1/10*P.6 + 1/10*P.7 + 1/10*P.8 + 1,
            1/10*P.1 + 1/10*P.2 + 1/10*P.3 + 1/5*P.4 + 1/5*P.5 + 1/5*P.6 + 1/10*P.7 + 1,
            1/10*P.1 + 1/10*P.2 + 1/10*P.3 + 1/5*P.4 + 1/5*P.5 + 1/10*P.6 + 1/10*P.7 + 1/10*P.8 + 1,
            1/10*P.2 + 1/10*P.3 + 1/5*P.4 + 1/5*P.5 + 1/5*P.6 + 1/10*P.7 + 1/10*P.8 + 1,
            1/11*P.1 + 2/11*P.2 + 2/11*P.3 + 3/11*P.4 + 2/11*P.5 + 1/11*P.6 + 1,
            1/11*P.1 + 1/11*P.2 + 2/11*P.3 + 3/11*P.4 + 2/11*P.5 + 1/11*P.6 + 1/11*P.7 + 1,
            1/11*P.1 + 1/11*P.2 + 2/11*P.3 + 2/11*P.4 + 2/11*P.5 + 2/11*P.6 + 1/11*P.7 + 1,
            1/11*P.1 + 1/11*P.2 + 2/11*P.3 + 2/11*P.4 + 2/11*P.5 + 1/11*P.6 + 1/11*P.7 + 1/11*P.8 + 1,
            1/11*P.1 + 1/11*P.2 + 1/11*P.3 + 2/11*P.4 + 2/11*P.5 + 2/11*P.6 + 1/11*P.7 + 1/11*P.8 + 1,
            1/11*P.2 + 1/11*P.3 + 2/11*P.4 + 2/11*P.5 + 2/11*P.6 + 2/11*P.7 + 1/11*P.8 + 1,
            1/12*P.1 + 1/6*P.2 + 1/6*P.3 + 1/4*P.4 + 1/6*P.5 + 1/12*P.6 + 1/12*P.7 + 1,
            1/12*P.1 + 1/12*P.2 + 1/6*P.3 + 1/4*P.4 + 1/6*P.5 + 1/6*P.6 + 1/12*P.7 + 1,
            1/12*P.1 + 1/12*P.2 + 1/6*P.3 + 1/4*P.4 + 1/6*P.5 + 1/12*P.6 + 1/12*P.7 + 1/12*P.8 + 1,
            1/12*P.1 + 1/12*P.2 + 1/6*P.3 + 1/6*P.4 + 1/6*P.5 + 1/6*P.6 + 1/12*P.7 + 1/12*P.8 + 1,
            1/12*P.1 + 1/12*P.2 + 1/12*P.3 + 1/6*P.4 + 1/6*P.5 + 1/6*P.6 + 1/6*P.7 + 1/12*P.8 + 1,
            1/13*P.1 + 2/13*P.2 + 2/13*P.3 + 3/13*P.4 + 2/13*P.5 + 2/13*P.6 + 1/13*P.7 + 1,
            1/13*P.1 + 2/13*P.2 + 2/13*P.3 + 3/13*P.4 + 2/13*P.5 + 1/13*P.6 + 1/13*P.7 + 1/13*P.8 + 1,
            1/13*P.1 + 1/13*P.2 + 2/13*P.3 + 3/13*P.4 + 3/13*P.5 + 2/13*P.6 + 1/13*P.7 + 1,
            1/13*P.1 + 1/13*P.2 + 2/13*P.3 + 3/13*P.4 + 2/13*P.5 + 2/13*P.6 + 1/13*P.7 + 1/13*P.8 + 1,
            1/13*P.1 + 1/13*P.2 + 2/13*P.3 + 2/13*P.4 + 2/13*P.5 + 2/13*P.6 + 2/13*P.7 + 1/13*P.8 + 1,
            1/14*P.1 + 1/7*P.2 + 1/7*P.3 + 3/14*P.4 + 3/14*P.5 + 1/7*P.6 + 1/14*P.7 + 1,
            1/14*P.1 + 1/7*P.2 + 1/7*P.3 + 3/14*P.4 + 1/7*P.5 + 1/7*P.6 + 1/14*P.7 + 1/14*P.8 + 1,
            1/14*P.1 + 1/14*P.2 + 1/7*P.3 + 3/14*P.4 + 3/14*P.5 + 1/7*P.6 + 1/14*P.7 + 1/14*P.8 + 1,
            1/14*P.1 + 1/14*P.2 + 1/7*P.3 + 3/14*P.4 + 1/7*P.5 + 1/7*P.6 + 1/7*P.7 + 1/14*P.8 + 1,
            1/15*P.1 + 2/15*P.2 + 2/15*P.3 + 4/15*P.4 + 1/5*P.5 + 2/15*P.6 + 1/15*P.7 + 1,
            1/15*P.1 + 2/15*P.2 + 2/15*P.3 + 1/5*P.4 + 1/5*P.5 + 2/15*P.6 + 1/15*P.7 + 1/15*P.8 + 1,
            1/15*P.1 + 2/15*P.2 + 2/15*P.3 + 1/5*P.4 + 2/15*P.5 + 2/15*P.6 + 2/15*P.7 + 1/15*P.8 + 1,
            1/15*P.1 + 1/15*P.2 + 2/15*P.3 + 1/5*P.4 + 1/5*P.5 + 2/15*P.6 + 2/15*P.7 + 1/15*P.8 + 1,
            1/16*P.1 + 1/8*P.2 + 3/16*P.3 + 1/4*P.4 + 3/16*P.5 + 1/8*P.6 + 1/16*P.7 + 1,
            1/16*P.1 + 1/8*P.2 + 1/8*P.3 + 1/4*P.4 + 3/16*P.5 + 1/8*P.6 + 1/16*P.7 + 1/16*P.8 + 1,
            1/16*P.1 + 1/8*P.2 + 1/8*P.3 + 3/16*P.4 + 3/16*P.5 + 1/8*P.6 + 1/8*P.7 + 1/16*P.8 + 1,
            1/16*P.1 + 1/16*P.2 + 1/8*P.3 + 3/16*P.4 + 3/16*P.5 + 3/16*P.6 + 1/8*P.7 + 1/16*P.8 + 1,
            2/17*P.1 + 2/17*P.2 + 3/17*P.3 + 4/17*P.4 + 3/17*P.5 + 2/17*P.6 + 1/17*P.7 + 1,
            1/17*P.1 + 2/17*P.2 + 3/17*P.3 + 4/17*P.4 + 3/17*P.5 + 2/17*P.6 + 1/17*P.7 + 1/17*P.8 + 1,
            1/17*P.1 + 2/17*P.2 + 2/17*P.3 + 4/17*P.4 + 3/17*P.5 + 2/17*P.6 + 2/17*P.7 + 1/17*P.8 + 1,
            1/17*P.1 + 2/17*P.2 + 2/17*P.3 + 3/17*P.4 + 3/17*P.5 + 3/17*P.6 + 2/17*P.7 + 1/17*P.8 + 1,
            1/9*P.1 + 1/9*P.2 + 1/6*P.3 + 2/9*P.4 + 1/6*P.5 + 1/9*P.6 + 1/18*P.7 + 1/18*P.8 + 1,
            1/18*P.1 + 1/9*P.2 + 1/6*P.3 + 2/9*P.4 + 1/6*P.5 + 1/9*P.6 + 1/9*P.7 + 1/18*P.8 + 1,
            1/18*P.1 + 1/9*P.2 + 1/9*P.3 + 2/9*P.4 + 1/6*P.5 + 1/6*P.6 + 1/9*P.7 + 1/18*P.8 + 1,
            2/19*P.1 + 2/19*P.2 + 3/19*P.3 + 4/19*P.4 + 3/19*P.5 + 2/19*P.6 + 2/19*P.7 + 1/19*P.8 + 1,
            1/19*P.1 + 2/19*P.2 + 3/19*P.3 + 4/19*P.4 + 3/19*P.5 + 3/19*P.6 + 2/19*P.7 + 1/19*P.8 + 1,
            1/19*P.1 + 2/19*P.2 + 2/19*P.3 + 4/19*P.4 + 4/19*P.5 + 3/19*P.6 + 2/19*P.7 + 1/19*P.8 + 1,
            1/10*P.1 + 1/10*P.2 + 3/20*P.3 + 1/5*P.4 + 3/20*P.5 + 3/20*P.6 + 1/10*P.7 + 1/20*P.8 + 1,
            1/20*P.1 + 1/10*P.2 + 3/20*P.3 + 1/5*P.4 + 1/5*P.5 + 3/20*P.6 + 1/10*P.7 + 1/20*P.8 + 1,
            2/21*P.1 + 2/21*P.2 + 1/7*P.3 + 4/21*P.4 + 4/21*P.5 + 1/7*P.6 + 2/21*P.7 + 1/21*P.8 + 1,
            1/21*P.1 + 2/21*P.2 + 1/7*P.3 + 5/21*P.4 + 4/21*P.5 + 1/7*P.6 + 2/21*P.7 + 1/21*P.8 + 1,
            1/11*P.1 + 1/11*P.2 + 3/22*P.3 + 5/22*P.4 + 2/11*P.5 + 3/22*P.6 + 1/11*P.7 + 1/22*P.8 + 1,
            1/22*P.1 + 3/22*P.2 + 3/22*P.3 + 5/22*P.4 + 2/11*P.5 + 3/22*P.6 + 1/11*P.7 + 1/22*P.8 + 1,
            2/23*P.1 + 3/23*P.2 + 3/23*P.3 + 5/23*P.4 + 4/23*P.5 + 3/23*P.6 + 2/23*P.7 + 1/23*P.8 + 1,
            2/23*P.1 + 2/23*P.2 + 4/23*P.3 + 5/23*P.4 + 4/23*P.5 + 3/23*P.6 + 2/23*P.7 + 1/23*P.8 + 1,
            1/12*P.1 + 1/8*P.2 + 1/6*P.3 + 5/24*P.4 + 1/6*P.5 + 1/8*P.6 + 1/12*P.7 + 1/24*P.8 + 1,
            2/25*P.1 + 3/25*P.2 + 4/25*P.3 + 6/25*P.4 + 4/25*P.5 + 3/25*P.6 + 2/25*P.7 + 1/25*P.8 + 1,
            1/13*P.1 + 3/26*P.2 + 2/13*P.3 + 3/13*P.4 + 5/26*P.5 + 3/26*P.6 + 1/13*P.7 + 1/26*P.8 + 1, 2/27*P.1 + 1/9*P.2 + 4/27*P.3 + 2/9*P.4 + 5/27*P.5 + 4/27*P.6 + 2/27*P.7 + 1/27*P.8 + 1,
            1/14*P.1 + 3/28*P.2 + 1/7*P.3 + 3/14*P.4 + 5/28*P.5 + 1/7*P.6 + 3/28*P.7 + 1/28*P.8 + 1,
            2/29*P.1 + 3/29*P.2 + 4/29*P.3 + 6/29*P.4 + 5/29*P.5 + 4/29*P.6 + 3/29*P.7 + 2/29*P.8 + 1
            ];
        else:
          error "Runtime error: Wrong Cartan name";
      end case;
    when "F":
      case n:
        when 4:
          P:=PolynomialRing(Rationals(),n);
          list:=
            [
            P.1 + 1,
            P.2 + 1,
            P.3 + 1,
            P.4 + 1,
            1/2*P.1 + 1/2*P.2 + 1,
            2/3*P.2 + 1/3*P.3 + 1,
            1/2*P.3 + 1/2*P.4 + 1,
            2/5*P.1 + 2/5*P.2 + 1/5*P.3 + 1,
            1/2*P.2 + 1/2*P.3 + 1,
            1/2*P.2 + 1/4*P.3 + 1/4*P.4 + 1,
            1/3*P.1 + 1/3*P.2 + 1/3*P.3 + 1,
            1/3*P.1 + 1/3*P.2 + 1/6*P.3 + 1/6*P.4 + 1,
            2/5*P.2 + 2/5*P.3 + 1/5*P.4 + 1,
            1/4*P.1 + 1/2*P.2 + 1/4*P.3 + 1,
            2/7*P.1 + 2/7*P.2 + 2/7*P.3 + 1/7*P.4 + 1,
            1/3*P.2 + 1/3*P.3 + 1/3*P.4 + 1,
            2/9*P.1 + 4/9*P.2 + 2/9*P.3 + 1/9*P.4 + 1,
            1/4*P.1 + 1/4*P.2 + 1/4*P.3 + 1/4*P.4 + 1,
            1/5*P.1 + 2/5*P.2 + 3/10*P.3 + 1/10*P.4 + 1,
            1/5*P.1 + 2/5*P.2 + 1/5*P.3 + 1/5*P.4 + 1,
            2/11*P.1 + 4/11*P.2 + 3/11*P.3 + 2/11*P.4 + 1,
            1/6*P.1 + 1/3*P.2 + 1/3*P.3 + 1/6*P.4 + 1,
            1/7*P.1 + 3/7*P.2 + 2/7*P.3 + 1/7*P.4 + 1,
            1/4*P.1 + 3/8*P.2 + 1/4*P.3 + 1/8*P.4 + 1
            ];
        else:
          error "Runtime error: Wrong Cartan name";
      end case;
    when "G":
      case n:
        when 2:
          P:=PolynomialRing(Rationals(),n);
          list:=
            [
            P.1 + 1,
            P.2 + 1,
            1/4*P.1 + 3/4*P.2 + 1,
            2/5*P.1 + 3/5*P.2 + 1,
            1/2*P.1 + 1/2*P.2 + 1,
            1/3*P.1 + 2/3*P.2 + 1
            ];
        else:
          error "Runtime error: Wrong Cartan name";
      end case;
    else:
      error "Runtime error: Wrong Cartan name";
  end case;
  return list;
end function;


function ReprDimFuncList(N);
   st:=string2tuple(N);
   return ReprDimFuncList_Xn(st[1],st[2]);
end function;


function ReprDimFunc_Xn(X,n);
  v:=ReprDimFuncList_Xn(X,n);
  return func<a|Integers()!(&*[Evaluate(i,a):i in v])>;
end function;


function ReprDimFunc(N);
   return ReprDimFuncList(N);
end function;




toSparse:=func<a|SparseMatrix(Matrix(1,#a,a))>;
fromSparse:=func<a|Eltseq(Matrix(a))>;
sparse_A:=func<a|SparseMatrix(1,1,[<1,1,a>])>;
sparse_B:=func<n|SparseMatrix(1,n,[<1,1,1>])>;
sparse_C:=func<n|SparseMatrix(1,n,[<1,n,1>])>;

//included for testing purposes
function IrreducibleSimpleLieSubalgebras_SLOW(N);
  //compute cand_list and initialize result_list 
  tt:=Cputime();
  cand_list:=[];
  result_list:=[[]:i in [1..N]];

  //A1:
  for j in [2..N] do
    Append(~(result_list[j]),<"A1",sparse_A(j-1)>);
  end for;
  //G2:
  if N ge 7 then 
    Append(~cand_list,"G2"); 
  end if;
  //F4:
  if N ge 26 then 
    Append(~cand_list,"F4"); 
  end if;
  //E6:
  if N ge 27 then 
    Append(~cand_list,"E6"); 
  end if;
  //E7:
  if N ge 56 then 
    Append(~cand_list,"E7"); 
  end if;
  //E8:
  if N ge 248 then 
    Append(~cand_list,"E8"); 
  end if;
  //A:
  if N ge 3 then
    search_limit:=Max(Floor(Sqrt(1/4+2*N)-1/2)+1,3); 
    //info on the representation of second-lowest dimension
    for j in [2..search_limit-1] do
      Append(~cand_list,"A" cat IntegerToString(j));
    end for;
    for j in [search_limit..N-1] do
      Append(~(result_list[j+1]),<"A" cat IntegerToString(j),sparse_B(j)>);
      Append(~(result_list[j+1]),<"A" cat IntegerToString(j),sparse_C(j)>);
    end for;
  end if;
  //B:
  if N ge 7 then
    search_limit:=Max(Floor((Sqrt(1+8*N)-1)/4)+1,7);
    //info on the representation of second-lowest dimension
    for j in [3..search_limit-1] do
      Append(~cand_list,"B" cat IntegerToString(j));
    end for;
    for j in [search_limit..((N-1) div 2)] do
      Append(~(result_list[2*j+1]),<"B" cat IntegerToString(j),sparse_B(j)>);
    end for;  
  end if;
  //C:
  if N ge 4 then
    search_limit:=Max(Floor((Sqrt(9+8*N)+1)/4)+1,4);
    //info on the representation of second-lowest dimension
    for j in [2..search_limit-1] do
      Append(~cand_list,"C" cat IntegerToString(j));
    end for;
    for j in [search_limit..(N div 2)] do
      Append(~(result_list[2*j]),<"C" cat IntegerToString(j),sparse_B(j)>);
    end for;
  end if;
  //D:
  if N ge 8 then
    search_limit:=Max(Floor((Sqrt(1+8*N)+1)/4)+1,8);
    for j in [4..search_limit-1] do
      Append(~cand_list,"D" cat IntegerToString(j));
    end for;
    for j in [search_limit..(N div 2)] do
      Append(~(result_list[2*j]),<"D" cat IntegerToString(j),sparse_B(j)>);
    end for;
  end if;
  vprintf SubSU, 1 : "cand_list: %o\n", cand_list;
  vprintf SubSU, 1 : "Time: %o\n", Cputime(tt);

  //search
  for rs in cand_list do
    ttt:=Cputime();
    el:=string2tuple(rs);
    X:=el[1];
    m:=el[2];
    dim_comp:=ReprDimFunc_Xn(X,m);  

    n:=0;
    start_el:=[0:i in [1..m]];
    next_list:={};
    for i in [1..m] do
      new_el:=start_el;
      new_el[i]+:=1;
      Include(~next_list,new_el);
    end for;  

    resume:=true;
    while resume do
      resume:=false;
      n+:=1;
      vprintf SubSU, 1 : "root system: %o, n: %o\n", rs, n;
      old_list:=next_list;
      next_list:={};

      for a in old_list do    
        t2:=Cputime();
        repr_dim:=dim_comp(a);
        if repr_dim le N then
          Append(~(result_list[repr_dim]),<rs,toSparse(a)>);
          resume:=true;
          for j in [1..m] do
            new_el:=a;
            new_el[j]+:=1;
            Include(~next_list,new_el);
          end for;
        end if;
        t2:=Cputime(t2);
      end for;
    end while;
    vprintf SubSU, 1 : "Time: %o\n", Cputime(ttt); 
  end for;
  vprintf SubSU, 1 : "Total time: %o\n", Cputime(tt);
  
  return result_list;
end function;

intrinsic IrreducibleSimpleSubalgebrasOfSU(N::RngIntElt) -> SeqEnum
{ A list of all irreducible simple subalgebras of the Lie algebras su(k),
  for 2 <= k <= N }

  //compute cand_list and initialize result_list 
  tt:=Cputime();
  cand_list:=[];
  result_list:=[[]:i in [1..N]];

  //A1:
  for j in [2..N] do
    Append(~(result_list[j]),<"A1",sparse_A(j-1)>);
  end for;
  //G2:
  if N ge 7 then 
    Append(~cand_list,"G2"); 
  end if;
  //F4:
  if N ge 26 then 
    Append(~cand_list,"F4"); 
  end if;
  //E6:
  if N ge 27 then 
    Append(~cand_list,"E6"); 
  end if;
  //E7:
  if N ge 56 then 
    Append(~cand_list,"E7"); 
  end if;
  //E8:
  if N ge 248 then 
    Append(~cand_list,"E8"); 
  end if;
  //A:
  if N ge 3 then
    pre_s:=Floor((q^2+3)/(3*q)) where q:=Root(81*N+3*Sqrt(-3+729*N^2),3);
    pre_s:=Max([x:x in [pre_s-1,pre_s,pre_s+1]|y le N where y:=(x+1)*x*(x-1)/6]);
    search_limit:=Max(pre_s,8);
    for j in [2..search_limit] do
      Append(~cand_list,"A" cat IntegerToString(j));
    end for;
    sl_1:=N-1;
    pre_s:=Floor(Sqrt(1/4+2*N)-1/2);
    sl_2:=Max([x:x in [pre_s-1,pre_s,pre_s+1]|y le N where y:=x*(x+1)/2]);
    pre_s:=Floor(Sqrt(1/4+2*N)-3/2);
    sl_3:=Max([x:x in [pre_s-1,pre_s,pre_s+1]|y le N where y:=(x+1)*(x+2)/2]);
    pre_s:=Floor(Sqrt(1+N)-1);
    sl_4:=Max([x:x in [pre_s-1,pre_s,pre_s+1]|y le N where y:=x*(x+2)]);
    for j in [search_limit+1..sl_1] do
      val:=j+1;
      Append(~(result_list[val]),<"A" cat IntegerToString(j),sparse_B(j)>);
      Append(~(result_list[val]),<"A" cat IntegerToString(j),sparse_C(j)>);
    end for;
    for j in [search_limit+1..sl_2] do
      val:=Integers()!(j*(j+1)/2);
      Append(~(result_list[val]),<"A" cat IntegerToString(j),SparseMatrix(1,j,[<1,2,1>])>);
      Append(~(result_list[val]),<"A" cat IntegerToString(j),SparseMatrix(1,j,[<1,j-1,1>])>);
    end for;
    for j in [search_limit+1..sl_3] do
      val:=Integers()!((j+1)*(j+2)/2);
      Append(~(result_list[val]),<"A" cat IntegerToString(j),SparseMatrix(1,j,[<1,1,2>])>);
      Append(~(result_list[val]),<"A" cat IntegerToString(j),SparseMatrix(1,j,[<1,j,2>])>);
    end for;
    for j in [search_limit+1..sl_4] do
      Append(~(result_list[j*(j+2)]),<"A" cat IntegerToString(j),SparseMatrix(1,j,[<1,1,1>,<1,j,1>])>);
    end for;
  end if;
  //B:
  if N ge 7 then
    pre_s:=Floor((q^2+3)/(6*q)) where q:=Root(81*N+3*Sqrt(-3+729*N^2),3);
    pre_s:=Max([x:x in [pre_s-1,pre_s,pre_s+1]|y le N where y:=(2*x+1)*(2*x-1)*x/3]);
    search_limit:=Max(pre_s,11); 
    for j in [3..search_limit] do
      Append(~cand_list,"B" cat IntegerToString(j));
    end for;
    sl_1:=Floor((N-1)/2);
    pre_s:=Floor((Sqrt(1+8*N)-1)/4);
    sl_2:=Max([x:x in [pre_s-1,pre_s,pre_s+1]|y le N where y:=(2*x+1)*x]);
    pre_s:=Floor((Sqrt(9+8*N)-3)/4);
    sl_3:=Max([x:x in [pre_s-1,pre_s,pre_s+1]|y le N where y:=x*(2*x+3)]);
    for j in [search_limit+1..sl_1] do
      val:=2*j+1;
      Append(~(result_list[val]),<"B" cat IntegerToString(j),sparse_B(j)>);
    end for;
    for j in [search_limit+1..sl_2] do
      val:=j*(2*j+1);
      Append(~(result_list[val]),<"B" cat IntegerToString(j),SparseMatrix(1,j,[<1,2,1>])>);
    end for;
    for j in [search_limit+1..sl_3] do
      val:=j*(2*j+3);
      Append(~(result_list[val]),<"B" cat IntegerToString(j),SparseMatrix(1,j,[<1,1,2>])>);
    end for;
  end if;
  //C:
  if N ge 4 then
    pre_s:=Floor((q^2+21+3*q)/(6*q)) where q:=Root(81+81*N+3*Sqrt(-300+1458*N+729*N^2),3);
    pre_s:=Max([x:x in [pre_s-1,pre_s,pre_s+1]|y le N where y:=2*(x-2)*x*(2*x+1)/3]);
    search_limit:=Max(pre_s,5); 
    for j in [2..search_limit] do
      Append(~cand_list,"C" cat IntegerToString(j));
    end for;
    sl_1:=Floor(N/2);
    pre_s:=Floor((Sqrt(9+8*N)+1)/4);
    sl_2:=Max([x:x in [pre_s-1,pre_s,pre_s+1]|y le N where y:=(x-1)*(2*x+1)]);
    pre_s:=Floor((Sqrt(1+8*N)-1)/4);
    sl_3:=Max([x:x in [pre_s-1,pre_s,pre_s+1]|y le N where y:=x*(2*x+1)]);
    for j in [search_limit+1..sl_1] do
      val:=2*j;
      Append(~(result_list[val]),<"C" cat IntegerToString(j),sparse_B(j)>);
    end for;
    for j in [search_limit+1..sl_2] do
      val:=(j-1)*(2*j+1);
      Append(~(result_list[val]),<"C" cat IntegerToString(j),SparseMatrix(1,j,[<1,2,1>])>);
    end for;
    for j in [search_limit+1..sl_3] do
      val:=j*(2*j+1);
      Append(~(result_list[val]),<"C" cat IntegerToString(j),SparseMatrix(1,j,[<1,1,2>])>);
    end for;
  end if;
  //D:
  if N ge 8 then
    pre_s:=Floor((q^2+3+3*q)/(6*q)) where q:=Root(81*N+3*Sqrt(-3+729*N^2),3);
    pre_s:=Max([x:x in [pre_s-1,pre_s,pre_s+1]|y le N where y:=2*x*(2*x-1)*(x-1)/3]);
    search_limit:=Max(pre_s,12);
    for j in [4..search_limit] do
      Append(~cand_list,"D" cat IntegerToString(j));
    end for;
    sl_1:=Floor(N/2);
    pre_s:=Floor((Sqrt(1+8*N)+1)/4);
    sl_2:=Max([x:x in [pre_s-1,pre_s,pre_s+1]|y le N where y:=(2*x-1)*x]);
    pre_s:=Floor((Sqrt(9+8*N)-1)/4);
    sl_3:=Max([x:x in [pre_s-1,pre_s,pre_s+1]|y le N where y:=(x+1)*(2*x-1)]);
    for j in [search_limit+1..sl_1] do
      val:=2*j;
      Append(~(result_list[val]),<"D" cat IntegerToString(j),sparse_B(j)>);
    end for;
    for j in [search_limit+1..sl_2] do
      val:=(2*j-1)*j;
      Append(~(result_list[val]),<"D" cat IntegerToString(j),SparseMatrix(1,j,[<1,2,1>])>);
    end for;
    for j in [search_limit+1..sl_3] do
      val:=(j+1)*(2*j-1);
      Append(~(result_list[val]),<"D" cat IntegerToString(j),SparseMatrix(1,j,[<1,1,2>])>);
    end for;
  end if;
  
  vprintf SubSU, 1 : "cand_list: %o\n", cand_list;
  

  //search
  for rs in cand_list do
    ttt:=Cputime();
    el:=string2tuple(rs);
    X:=el[1];
    m:=el[2];
    ti_dim:=Cputime();
    dim_comp:=ReprDimFunc_Xn(X,m);      
     
    //optimized initialization phase
    if (X eq "A") and (m gt 1) then
      ti_w:=Cputime();
      n:=1;

      vprintf SubSU, 1 : "root system: %o, n: %o\n", rs, n;
      vprintf SubSU, 1 : " dimension formula, timing: %o\n", Cputime(ti_dim);

      max_j:=(m div 2);
      if IsOdd(m) then 
        max_j+:=1;
      end if;
      next_list:={};
      pre_list:={};
      j:=1;
      start_el:=[0:i in [1..m]];
      while j le max_j do
        a:=start_el;
        a[j]+:=1;
        repr_dim:=dim_comp(a);
        if repr_dim le N then
          a_set:={a,Reverse(a)};
          for el in a_set do
            Append(~(result_list[repr_dim]),<rs,toSparse(el)>);
            resume:=true;
            Include(~pre_list,<el,Support(Vector(el))>);
            for j in Support(Vector(el)) do
              new_el:=el;
              new_el[j]+:=1;
              Include(~next_list,new_el);
            end for;
          end for;
        else
          vprintf SubSU, 1 : " broke at step: %o\n", j;
          break;
        end if;
        j+:=1;
      end while;
      pre_list:=SetToSequence(pre_list);
      num_pre:=#pre_list;
      while #pre_list gt 1 do
         b:=pre_list[#pre_list];
         Prune(~pre_list);
         for el in pre_list do
           supp:=el[2] diff b[2];
           if (#supp eq 1) and (#(b[2] diff el[2]) eq 1) and (&+[Abs(el[1,i]-b[1,i]):i in [1..m]] eq 2) then
              new_el:=b[1];
              new_el[Rep(supp)]+:=1;
              Include(~next_list,new_el);
           end if;
         end for;
      end while;

      vprintf SubSU, 1 : " timing: %o,", Cputime(ti_w);
      vprintf SubSU, 1 : " #pre_list : %o,", num_pre;
      vprintf SubSU, 1 : " #next_list: %o\n", #next_list;

    elif (X eq "B") and (m gt 1) then
      ti_w:=Cputime();
      n:=1;

      vprintf SubSU, 1 : "root system: %o, n: %o\n", rs, n;
      vprintf SubSU, 1 : " dimension formula, timing: %o\n", Cputime(ti_dim); 

      max_j:=m-1;
      next_list:={};
      pre_list:={};
      j:=1;
      start_el:=[0:i in [1..m]];
      if 2^m le N then
        a:=start_el;
        a[m]+:=1;
        repr_dim:=2^m;
        Append(~(result_list[repr_dim]),<rs,toSparse(a)>);
        Include(~pre_list,<a,Support(Vector(a))>);
        for j in Support(Vector(a)) do
           new_el:=a;
           new_el[j]+:=1;
           Include(~next_list,new_el);
        end for;    
      end if;
      while j le max_j do
        a:=start_el;
        a[j]+:=1;
        repr_dim:=dim_comp(a);
        if repr_dim le N then          
          Append(~(result_list[repr_dim]),<rs,toSparse(a)>);
          Include(~pre_list,<a,Support(Vector(a))>);
          for j in Support(Vector(a)) do
             new_el:=a;
             new_el[j]+:=1;
             Include(~next_list,new_el);
          end for;
        else
          vprintf SubSU, 1 : " broke at step: %o\n", j;

          break;
        end if;
        j+:=1;
      end while;
      pre_list:=SetToSequence(pre_list);
      num_pre:=#pre_list;
      while #pre_list gt 1 do
         b:=pre_list[#pre_list];
         Prune(~pre_list);
         for el in pre_list do
           supp:=el[2] diff b[2];
           if (#supp eq 1) and (#(b[2] diff el[2]) eq 1) and (&+[Abs(el[1,i]-b[1,i]):i in [1..m]] eq 2) then
              new_el:=b[1];
              new_el[Rep(supp)]+:=1;
              Include(~next_list,new_el);
           end if;
         end for;
      end while;
      vprintf SubSU, 1 : " timing: %o,", Cputime(ti_w);
      vprintf SubSU, 1 : " #pre_list : %o,", num_pre;
      vprintf SubSU, 1 : " #next_list: %o\n", #next_list;
    elif (X eq "D") and (m gt 2) then
      ti_w:=Cputime();
      n:=1;
      vprintf SubSU, 1 : "root system: %o, n: %o\n", rs, n;
      vprintf SubSU, 1 : " dimension formula, timing: %o\n", Cputime(ti_dim);
      max_j:=m-2;
      next_list:={};
      pre_list:={};
      j:=1;
      start_el:=[0:i in [1..m]];
      if 2^(m-1) le N then
        a_1:=start_el;
        a_1[m-1]+:=1;
        a_2:=start_el;
        a_2[m]+:=1;
        repr_dim:=2^(m-1);
        a_set:={a_1,a_2};
        for el in a_set do
          Append(~(result_list[repr_dim]),<rs,toSparse(el)>);
          Include(~pre_list,<el,Support(Vector(el))>);
          for j in Support(Vector(el)) do
            new_el:=el;
            new_el[j]+:=1;
            Include(~next_list,new_el);
          end for;
        end for;
      end if;
      while j le max_j do
        a:=start_el;
        a[j]+:=1;
        repr_dim:=dim_comp(a);
        if repr_dim le N then          
          Append(~(result_list[repr_dim]),<rs,toSparse(a)>);
          Include(~pre_list,<a,Support(Vector(a))>);
          for j in Support(Vector(a)) do
             new_el:=a;
             new_el[j]+:=1;
             Include(~next_list,new_el);
          end for;
        else
          vprintf SubSU, 1 : " broke at step: %o\n", j;
          break;
        end if;
        j+:=1;
      end while;
      pre_list:=SetToSequence(pre_list);
      num_pre:=#pre_list;
      while #pre_list gt 1 do
         b:=pre_list[#pre_list];
         Prune(~pre_list);
         for el in pre_list do
           supp:=el[2] diff b[2];
           if (#supp eq 1) and (#(b[2] diff el[2]) eq 1) and (&+[Abs(el[1,i]-b[1,i]):i in [1..m]] eq 2) then
              new_el:=b[1];
              new_el[Rep(supp)]+:=1;
              Include(~next_list,new_el);
           end if;
         end for;
      end while;
      vprintf SubSU, 1 : " timing: %o,", Cputime(ti_w);
      vprintf SubSU, 1 : " #pre_list : %o,", num_pre;
      vprintf SubSU, 1 : " #next_list: %o\n", #next_list;
    elif (X eq "C") and (m gt 3) then
      ti_w:=Cputime();
      n:=1;
      vprintf SubSU, 1 : "root system: %o, n: %o\n", rs, n;
      vprintf SubSU, 1 : " dimension formula, timing: %o\n", Cputime(ti_dim);
      max_j:=m;
      next_list:={};
      pre_list:={};
      j:=1;
      start_el:=[0:i in [1..m]];
      while j le max_j do
        a:=start_el;
        a[j]+:=1;
        repr_dim:=dim_comp(a);
        if repr_dim le N then          
          Append(~(result_list[repr_dim]),<rs,toSparse(a)>);
          Include(~pre_list,<a,Support(Vector(a))>);
          for j in Support(Vector(a)) do
             new_el:=a;
             new_el[j]+:=1;
             Include(~next_list,new_el);
          end for;
        else
          vprintf SubSU, 1 : " broke at step: %o\n", j;
          j2:=m;
          while j2 gt j do
            a:=start_el;
            a[j2]+:=1;
            repr_dim:=dim_comp(a);
            if repr_dim le N then          
              Append(~(result_list[repr_dim]),<rs,toSparse(a)>);
              Include(~pre_list,<a,Support(Vector(a))>);
              for j in Support(Vector(a)) do
                 new_el:=a;
                 new_el[j]+:=1;
                 Include(~next_list,new_el);
              end for;
            else
              vprintf SubSU, 1 : "  broke at step: %o\n", j2;
              break;
            end if;
            j2-:=1;
          end while;
          break;
        end if;
        j+:=1;
      end while;
      pre_list:=SetToSequence(pre_list);
      num_pre:=#pre_list;
      while #pre_list gt 1 do
         b:=pre_list[#pre_list];
         Prune(~pre_list);
         for el in pre_list do
           supp:=el[2] diff b[2];
           if (#supp eq 1) and (#(b[2] diff el[2]) eq 1) and (&+[Abs(el[1,i]-b[1,i]):i in [1..m]] eq 2) then
              new_el:=b[1];
              new_el[Rep(supp)]+:=1;
              Include(~next_list,new_el);
           end if;
         end for;
      end while;
      vprintf SubSU, 1 : " timing: %o,", Cputime(ti_w);
      vprintf SubSU, 1 : " #pre_list : %o,", num_pre;
      vprintf SubSU, 1 : " #next_list: %o\n", #next_list;
    else
      n:=0;
      start_el:=[0:i in [1..m]];
      next_list:={};
      for i in [1..m] do
        new_el:=start_el;
        new_el[i]+:=1;
        Include(~next_list,new_el);
      end for;  
    end if;

    //optimized search phase
    resume:=true;
    while resume do
      ti_w:=Cputime();
      resume:=false;
      n+:=1;

      vprintf SubSU, 1 : "root system: %o, n: %o\n", rs, n;
      if n eq 1 then
        vprintf SubSU, 1 : " dimension formula, timing: %o\n", Cputime(ti_dim);
      end if;

      old_list:=next_list;
      next_list:={};
      pre_list:={};
      for a in old_list do    
        t2:=Cputime();
        repr_dim:=dim_comp(a);
        if repr_dim le N then
          Append(~(result_list[repr_dim]),<rs,toSparse(a)>);
          resume:=true;
          Include(~pre_list,<a,Support(Vector(a))>);
          for j in Support(Vector(a)) do
            new_el:=a;
            new_el[j]+:=1;
            Include(~next_list,new_el);
          end for;
        end if;
        t2:=Cputime(t2);
      end for;
      pre_list:=SetToSequence(pre_list);
      num_pre:=#pre_list;
      while #pre_list gt 1 do
         b:=pre_list[#pre_list];
         Prune(~pre_list);
         for el in pre_list do
           supp:=el[2] diff b[2];
           if (#supp eq 1) and (#(b[2] diff el[2]) eq 1) and (&+[Abs(el[1,i]-b[1,i]):i in [1..m]] eq 2) then
              new_el:=b[1];
              new_el[Rep(supp)]+:=1;
              Include(~next_list,new_el);
           end if;
         end for;
      end while;
      vprintf SubSU, 1 : " timing: %o,", Cputime(ti_w);
      vprintf SubSU, 1 : " #pre_list : %o,", num_pre;
      vprintf SubSU, 1 : " #next_list: %o\n", #next_list;
    end while;

    vprintf SubSU, 1 : "Time: %o\n", Cputime(ttt);

  end for;

  vprintf SubSU, 1 : "Total time: %o\n", Cputime(tt);

  return result_list;
end intrinsic;



type:=function(rd_str,a);
  alpha:=rd_str[1];
  numeric:=StringToInteger(rd_str[2..#rd_str]);

  case alpha:
    when "A":
      if (numeric eq 1) or (&and{a[j] eq a[numeric-j+1]:j in [1..(numeric div 2)]}) then
        case numeric mod 4:
          when 0,2,3:
            return 1; 
          when 1:
            if IsEven(a[((numeric-1) div 2)+1]) then
              return 1;
            else
              return -1;
            end if;
        end case;
      else
        return 0;
      end if;
    when "B":
      case numeric mod 4:
        when 0,3:
          return 1;
        when 1,2:
          if IsEven(a[numeric]) then
            return 1;
          else
            return -1;
          end if;
      end case;
    when "C":
      if IsEven(&+[a[2*i+1]:i in [0..(numeric-1) div 2]]) then
        return 1;
      else
        return -1;
      end if;
    when "D":
      if IsEven(numeric) or (a[numeric] eq a[numeric-1]) then
        case numeric mod 4:
          when 0,1,3:
            return 1;
          when 2:
            if IsEven(a[numeric]+a[numeric-1]) then
              return 1;
            else
              return -1;
            end if;
        end case;
      else
        return 0;
      end if;
    when "E":
      case numeric:
        when 6:
          if (a[1] eq a[6]) and (a[3] eq a[5]) then
            return 1;
          else
            return 0;
          end if;
        when 7:
          if IsEven(a[2]+a[5]+a[7]) then
            return 1;
          else
            return -1;
          end if; 
        when 8:
          return 1;
      end case; 
    when "F":
      return 1;
    when "G":
      return 1;
  end case;
end function;

type_sparse:=function(rd_str,a);
  alpha:=rd_str[1];
  numeric:=StringToInteger(rd_str[2..#rd_str]);

  case alpha:
    when "A":
      if (numeric eq 1) or (ReverseColumns(a) eq a) then
        case numeric mod 4:
          when 0,2,3:
            return 1; 
          when 1:
            if IsEven(a[1,((numeric-1) div 2)+1]) then
              return 1;
            else
              return -1;
            end if;
        end case;
      else
        return 0;
      end if;
    when "B":
      case numeric mod 4:
        when 0,3:
          return 1;
        when 1,2:
          if IsEven(a[1,numeric]) then
            return 1;
          else
            return -1;
          end if;
      end case;
    when "C":
      if IsEven(&+[Integers()|a[i[1],i[2]]:i in Support(a)|IsOdd(i[2]) and i[2] le numeric]) then
        return 1;
      else
        return -1;
      end if;
    when "D":
      if IsEven(numeric) or (a[1,numeric] eq a[1,numeric-1]) then
        case numeric mod 4:
          when 0,1,3:
            return 1;
          when 2:
            if IsEven(a[1,numeric]+a[1,numeric-1]) then
              return 1;
            else
              return -1;
            end if;
        end case;
      else
        return 0;
      end if;
    when "E":
      case numeric:
        when 6:
          if (a[1,1] eq a[1,6]) and (a[1,3] eq a[1,5]) then
            return 1;
          else
            return 0;
          end if;
        when 7:
          if IsEven(a[1,2]+a[1,5]+a[1,7]) then
            return 1;
          else
            return -1;
          end if; 
        when 8:
          return 1;
      end case; 
    when "F":
      return 1;
    when "G":
      return 1;
  end case;
end function;

compare_weights:=function(w1,w2);
  for ind in Sort(SetToSequence({k[2]:k in (Support(w1) cat Support(w2))})) do
    if w1[1,ind] lt w2[1,ind] then
      return -1;
    elif w1[1,ind] gt w2[1,ind] then
      return 1;
    end if;
  end for;
  return 0;
end function;

compare_names:=function(one,two)
  alpha_one:=one[1];
  numeric_one:=StringToInteger(one[2..#one]);
  alpha_two:=two[1];
  numeric_two:=StringToInteger(two[2..#two]);
  if alpha_one lt alpha_two then
    return -1;
  elif alpha_one eq alpha_two then
    if numeric_one lt numeric_two then
      return -1;
    elif numeric_one eq numeric_two then
      return 0;
    else
      return 1;
    end if;
  else
    return 1;
  end if;
end function;


irred_simple:=recformat<algebra:MonStgElt,weights,type:Integers(),parent:MonStgElt>;

IRRED_SIMPLE:=recformat<algebra:MonStgElt,weights,type:Integers()>;

compare_irred:=function(el1,el2)
  tr:=compare_names(el1`algebra,el2`algebra);
  if tr eq -1 then
    return -1;
  elif tr eq 1 then
    return 1;
  else
    return compare_weights((el1`weights)[1],(el2`weights)[1]);
  end if;  
end function;

compare_node:=function(el1,el2)
  return compare_irred(el1[2],el2[2]);
end function;

intrinsic IrreducibleSimpleSubalgebraTreeSU(Q::SeqEnum[SeqEnum[Tup]], dim::RngIntElt) -> GrphDir
{ The subalgebra tree for the list Q of irreducible subalgebras of dimension k}
  list := Q[dim];
  list_irred_simple:=[rec<irred_simple|algebra:=i[1],weights:=i[2]>:i in list];

  // compute type
  for i in [1..#list_irred_simple] do
      (list_irred_simple[i])`type:=type_sparse((list_irred_simple[i])`algebra,(list_irred_simple[i])`weights);
  end for;

  //compute the name of the parent algebra (=parent) 
  for i in [1..#list_irred_simple] do
    alpha:=((list_irred_simple[i])`algebra)[1];
    len:=#((list_irred_simple[i])`algebra);
    numeric:=StringToInteger(((list_irred_simple[i])`algebra)[2..len]);

    //first treat the non-maximal cases
    case alpha:
      when "A":
        if (numeric eq 1) and ((list_irred_simple[i])`weights eq toSparse([6])) then
          (list_irred_simple[i])`parent:="G2";
        end if;
        if (numeric eq 5) and ((list_irred_simple[i])`weights eq toSparse([0,1,0,1,0])) then
          (list_irred_simple[i])`parent:="C10";
        end if;
        if (numeric ge 2) and (((list_irred_simple[i])`weights eq SparseMatrix(1,numeric,[<1,1,2>,<1,2,1>])) or ((list_irred_simple[i])`weights eq SparseMatrix(1,numeric,[<1,numeric-1,1>,<1,numeric,2>]))) then
          (list_irred_simple[i])`parent:="A" cat IntegerToString(numeric*(numeric+3) div 2);
        end if;
        if (numeric ge 4) and (((list_irred_simple[i])`weights eq SparseMatrix(1,numeric,[<1,1,1>,<1,3,1>])) or ((list_irred_simple[i])`weights eq SparseMatrix(1,numeric,[<1,numeric-2,1>,<1,numeric,1>]))) then
          (list_irred_simple[i])`parent:="A" cat IntegerToString((numeric-1)*(numeric+2) div 2);
        end if;
      when "B":
        if (numeric eq 4) and ((list_irred_simple[i])`weights eq toSparse([1,0,0,1])) then
          (list_irred_simple[i])`parent:="D8";
        end if;
        if (IsOdd(numeric)) and (numeric ge 3) and (Support((list_irred_simple[i])`weights) eq  [<1,numeric>]) then
          if not ((numeric eq 3) and ((list_irred_simple[i])`weights eq toSparse([0,0,1]))) then
            (list_irred_simple[i])`parent:="D" cat IntegerToString(numeric+1);
          end if;
        end if;
      when "C":
        if numeric eq 3 then
          if (list_irred_simple[i])`weights eq toSparse([1,2,0]) then
            (list_irred_simple[i])`parent:="C7";
          end if;
          if (list_irred_simple[i])`weights eq toSparse([0,2,0]) then
            (list_irred_simple[i])`parent:="C7";
          end if;
        end if;
      when "D":
        if (numeric eq 5) and (((list_irred_simple[i])`weights eq toSparse([0,1,0,1,0])) or ((list_irred_simple[i])`weights eq toSparse([0,1,0,0,1]))) then
          (list_irred_simple[i])`parent:="A15";
        end if;
        if numeric eq 6 then
          if (list_irred_simple[i])`weights eq toSparse([0,0,0,1,0,0]) then
            (list_irred_simple[i])`parent:="C16";
          end if;
          if ((list_irred_simple[i])`weights eq toSparse([0,0,1,0,1,0])) or ((list_irred_simple[i])`weights eq toSparse([0,0,1,0,0,1])) then
            (list_irred_simple[i])`parent:="C16";
          end if;
        end if;
      when "E":
        if numeric eq 6 then
          if ((list_irred_simple[i])`weights eq toSparse([0,0,0,0,1,0])) or ((list_irred_simple[i])`weights eq toSparse([0,0,1,0,0,0])) then
            (list_irred_simple[i])`parent:="A26";
          end if;
          if ((list_irred_simple[i])`weights eq toSparse([0,1,1,0,0,0])) or ((list_irred_simple[i])`weights eq toSparse([0,1,0,0,1,0])) then
            (list_irred_simple[i])`parent:="A26";
          end if;
        end if;
        if numeric eq 7 then
          if (list_irred_simple[i])`weights eq toSparse([0,0,0,0,0,1,0]) then
            (list_irred_simple[i])`parent:="C28";
          end if;
          if (list_irred_simple[i])`weights eq toSparse([0,0,0,0,1,0,0]) then
            (list_irred_simple[i])`parent:="C28";
          end if;
          if (list_irred_simple[i])`weights eq toSparse([0,0,0,1,0,0,0]) then
            (list_irred_simple[i])`parent:="C28";
          end if;
          if (list_irred_simple[i])`weights eq toSparse([0,1,1,0,0,0,0]) then
            (list_irred_simple[i])`parent:="C28";
          end if;
        end if;
      when "G":
        if (numeric eq 2) and (((list_irred_simple[i])`weights)[1,2] eq 0) and (((list_irred_simple[i])`weights)[1,1] ge 2) then
          (list_irred_simple[i])`parent:="B3";
        end if;
    end case;

    //next treat the maximal cases
    //if (dim eq 2) and ((list_irred_simple[i])`algebra eq "A1") then
    //  //do nothing, no parent
    //end if;
    if (dim eq 5) and ((list_irred_simple[i])`algebra eq "C2") then
      (list_irred_simple[i])`parent:="A4";
    end if;
    if (dim eq 6) and ((list_irred_simple[i])`algebra eq "A3") then
      (list_irred_simple[i])`parent:="A5";
    end if;
    if (dim eq 3) and ((list_irred_simple[i])`algebra eq "A1") then
      (list_irred_simple[i])`parent:="A2";
    end if;
    if not (assigned (list_irred_simple[i])`parent) and not ((dim eq 2) and ((list_irred_simple[i])`algebra eq "A1")) then
      case (list_irred_simple[i])`type:
        when 0:
          (list_irred_simple[i])`parent:="A" cat IntegerToString(dim-1);
        when 1:
          if IsEven(dim) then
            (list_irred_simple[i])`parent:="D" cat IntegerToString(dim div 2);
          else
            (list_irred_simple[i])`parent:="B" cat IntegerToString((dim-1) div 2);
          end if;
        when -1:
          (list_irred_simple[i])`parent:="C" cat IntegerToString(dim div 2);
      end case;
      if (list_irred_simple[i])`parent eq (list_irred_simple[i])`algebra then
        if (list_irred_simple[i])`type eq 0 then
          delete (list_irred_simple[i])`parent;
        else
          (list_irred_simple[i])`parent:="A" cat IntegerToString(dim-1);
        end if;
      end if;
    end if;
  end for;

  // change name for "C2" and "A3" according to the type
  for i in [1..#list_irred_simple] do
    if (list_irred_simple[i])`algebra eq "C2" then
      if (list_irred_simple[i])`type eq 1 then
         (list_irred_simple[i])`algebra:="B2";
         (list_irred_simple[i])`weights:=ReverseColumns((list_irred_simple[i])`weights);
      end if;
    end if;
    if (list_irred_simple[i])`algebra eq "A3" then
      if (list_irred_simple[i])`type eq 1 then
         (list_irred_simple[i])`algebra:="D3";
         a:=fromSparse((list_irred_simple[i])`weights);
         (list_irred_simple[i])`weights:=toSparse([a[2],a[1],a[3]]);
      end if;
    end if;
  end for;

  //group highest weight with respect to outer automorphisms
  for i in [1..#list_irred_simple] do
    alpha:=((list_irred_simple[i])`algebra)[1];
    len:=#((list_irred_simple[i])`algebra);
    numeric:=StringToInteger(((list_irred_simple[i])`algebra)[2..len]);
    case alpha:
      when "A":
        (list_irred_simple[i])`weights:={(list_irred_simple[i])`weights,ReverseColumns((list_irred_simple[i])`weights)};
      when "D":
        if numeric eq 4 then
           (list_irred_simple[i])`weights:={toSparse(a[k]) where k:=[1,2,3,4]^j:j in sub<Sym(4)|[(1,3),(1,4),(3,4)]>} where a:=fromSparse((list_irred_simple[i])`weights);
        else
           (list_irred_simple[i])`weights:={(list_irred_simple[i])`weights,SwapColumns((list_irred_simple[i])`weights,numeric-1,numeric)};
        end if;
      when "E":
        if numeric eq 6 then
           (list_irred_simple[i])`weights:={(list_irred_simple[i])`weights,toSparse([a[6],a[2],a[5],a[4],a[3],a[1]])} where a:=fromSparse((list_irred_simple[i])`weights);
        else
           (list_irred_simple[i])`weights:={(list_irred_simple[i])`weights};
        end if;
      else
        (list_irred_simple[i])`weights:={(list_irred_simple[i])`weights};
    end case;
    (list_irred_simple[i])`weights:=SetToSequence((list_irred_simple[i])`weights);
    Sort(~((list_irred_simple[i])`weights),compare_weights);
    Reverse(~((list_irred_simple[i])`weights));
  end for;
  new_list_irred_simple:=[];
  for el in list_irred_simple do
    if not exists{k:k in new_list_irred_simple|(el`algebra eq k`algebra) and (el`weights eq k`weights)} then
      Append(~new_list_irred_simple,el);
    end if;
  end for;
  list_irred_simple:=new_list_irred_simple;
  delete new_list_irred_simple;
  
  //build subalgebra graph
  Gr:=Digraph<#list_irred_simple|>;
  for j in [1..#list_irred_simple] do
    if assigned list_irred_simple[j]`parent then
      cand:=[k:k in [1..#list_irred_simple]|list_irred_simple[k]`algebra eq list_irred_simple[j]`parent];  
      if #cand gt 1 then
        //does not happen very often
        vprintf SubSU, 1 : "Warning: Potential non-unique parent in dimension %o, ", dim;
        alpha:=((list_irred_simple[j])`algebra)[1];
        len:=#((list_irred_simple[j])`algebra);
        numeric:=StringToInteger(((list_irred_simple[j])`algebra)[2..len]);
        case alpha:
          when "B":
            if (IsOdd(numeric)) and (numeric ge 3) and (Support(Rep((list_irred_simple[j])`weights)) eq  [<1,numeric>]) then
              if not ((numeric eq 3) and (Rep((list_irred_simple[j])`weights) eq toSparse([0,0,1]))) then
                s:=SparseMatrix(1,numeric+1,[<1,numeric+1,Rep((list_irred_simple[j])`weights)[1,numeric]>]);
                cand:=[i:i in  cand|s in (list_irred_simple[i])`weights];                
              end if;
            end if;
          when "G":
            if (numeric eq 2) and (Rep((list_irred_simple[j])`weights)[1,2] eq 0) and (Rep((list_irred_simple[j])`weights)[1,1] ge 2) then
              s:=toSparse([Rep((list_irred_simple[j])`weights)[1,1],0,0]);
              cand:=[i:i in  cand|s in (list_irred_simple[i])`weights];
            end if;
        end case;
        if #cand ne 1 then
          //should not happen
          error "\nError: non-unique parent in dimension", dim, "\n";
        else 
          vprintf SubSU, 1 : "Resolved!\n";
        end if;
      end if;
      AddEdge(~Gr,cand[1],j);
    end if;
  end for;

  //correct the enumeration of the nodes in the subalgebra graph
  build_newGr:=procedure(v_Gr,~num,~gr)
    curr_num:=num;
    el:=list_irred_simple[Index(v_Gr)];
    AssignLabel(~gr,VertexSet(gr)!curr_num,rec<IRRED_SIMPLE|algebra:=el`algebra,weights:=el`weights,type:=el`type>);
    on:=SetToSequence(OutNeighbors(v_Gr));
    if #on gt 0 then
      label_seq:=[<el,list_irred_simple[Index(el)]>:el in on];
      first_seq:=[];
      if IsRoot(v_Gr) then
        if IsEven(dim) then
          test1:="C" cat IntegerToString(dim div 2);
          if exists(em){i:i in label_seq|i[2]`algebra eq test1} then
            ind:=Rep([k:k in [1..#label_seq]|em[1] eq label_seq[k,1]]);
            Remove(~label_seq,ind);
            Append(~first_seq,em);
          end if;      
          test1:="D" cat IntegerToString(dim div 2);
          if exists(em){i:i in label_seq|i[2]`algebra eq test1} then
            ind:=Rep([k:k in [1..#label_seq]|em[1] eq label_seq[k,1]]);
            Remove(~label_seq,ind);
            Append(~first_seq,em);
          end if;            
        else
          test1:="B" cat IntegerToString((dim-1) div 2);
          if exists(em){i:i in label_seq|i[2]`algebra eq test1} then
            ind:=Rep([k:k in [1..#label_seq]|em[1] eq label_seq[k,1]]);
            Remove(~label_seq,ind);
            Append(~first_seq,em);
          end if;            
        end if;
      end if;
      Sort(~label_seq,compare_node);
      on:=[i[1]:i in first_seq] cat [i[1]:i in label_seq];
    end if;

    for i in on do
      num+:=1;
      AddEdge(~gr,curr_num,num);
      $$(i,~num,~gr);
    end for;
  end procedure;

  newGr:=Digraph<#list_irred_simple|>;
  val:=1;
  build_newGr(Root(Gr),~val,~newGr);

  //sanity check  
  we:=[i:i in Labels(VertexSet(newGr))];
  for j in we do
    if #[i:i in we|compare_irred(i,j) eq 0] ne 1 then    
      error "Error: unkown error in dimension", dim, "\n";
    end if;
  end for;

  return newGr;
end intrinsic;

