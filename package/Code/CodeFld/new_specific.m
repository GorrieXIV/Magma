freeze;

intrinsic DoublyCirculantQRCodeGF4(m::RngIntElt,a::RngElt)->Code
{Construction of a doubly circulant linear code C=[2m,m] over GF(4).}
/* see:
 
  Philipp Gaborit,
  "Quadratic Double Circulant Codes over Fields",
  Journal of Combinatorial Theory, Series A, vol. 97, pp. 85-107 (2002).
 
*/
  require m ge 2: "First argument must be >= 2";
  require IsPrimePower(m): Sprintf("Argument 1 (%o) is not a prime power",m);
  require a in [0,1]: "Second argument must be 0 or 1";
 
  w:=GF(4).1;
  chi:=func<x|x eq a select 1 else IsSquare(x) and x ne 0 select w else w^2>;
  chi:=func<x|x eq a select a else IsSquare(x) select w else w^2>;
 
  chi:=func<x|x eq 0 select a else IsSquare(x) select w else w^2>;
 
  Q:=MatrixRing(GF(4),m)![chi(a-b):a,b in GF(m)];
 
  if a eq 0 then
    return LinearCode(HorizontalJoin(Q^0,Q));
  else
    B:=KMatrixSpace(GF(4),m+1,2*m+2)!0;
    InsertBlock(~B,Q,2,m+3);
    for i:=1 to m+1 do
      B[i,i]:=1;
    end for;
    for i:=2 to m+1 do
      B[i,m+2]:=1;
      B[1,m+1+i]:=1;
    end for;
    return LinearCode(B);
  end if;
end intrinsic;
