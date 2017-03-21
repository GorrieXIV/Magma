freeze;

///////////////////////////////////////////////////////////////////
// INPUT:
//   (1) (black box with Order oracle) group <gp>
//   (2) involution <i> of <gp>
// OUTPUT: list of one or two elements commuting with <i>
Comm := func< g,h | g^-1*h^-1*g*h >;

//////////////////////////////////////////////////////////
// INPUT: 
//   (1) (black box) group <gp>
//   (2) element <x> supergroup of <gp>
// OUTPUT: <true> iff <x> is centralised by <gp>
IsCentralisedBy := function(gp, x)
local  central, y;
   central := true;
   for y in Generators(gp) do
      central := central and IsIdentity(Comm(x, y));
   end for;
return central;
end function;

/////////////////////////////////////////////////////////////////////////////////////
// INPUT:
// (1) a matrix group <gp>
// (2) the (natural) vector space <V> upon which <gp> acts
// OUTPUT: the support of <gp>
GroupSupport := function(gp, V)
local  bas, x, b;
   bas := [];
   for x in [gp.i : i in [1..Ngens(gp)]] do
      for b in Basis(V) do
         Append(~bas, b-b*x);
      end for;
   end for;
return sub< V | bas >;
//return VectorSpace(bas);
end function;

/////////////////////////////////////////////////////////////////////////////////////
// INPUT:
// (1) a matrix
// (2) s subspace preserved by matrix
// OUTPUT: the transformation induced by the matrix on the subspace
ActionOnSubspace := function(x, W)
//return List( Basis(W), w->Coefficients(Basis(W), w*x) );
return Matrix([ Coordinates(W, w*x) : w in Basis(W) ]);
end function;

/////////////////////////////////////////////////////////////////////////////////////
// INPUT:
// (1) a matrix group <gp>
// (2) the (natural) vector space <V> upon which <gp> acts
// OUTPUT: the subspace of <V> centralised by <gp>
GroupCentralisedSpace := function(gp, V)
local  cent, x, nbasis;
   cent := V;
   for x in [gp.i : i in [1..Ngens(gp)]] do
      y := MatrixAlgebra(BaseRing(gp), Degree(gp))!x;
      nbasis := Nullspace( y - y^0 );
      cent := cent meet nbasis;
   end for;
return cent;
end function;

////////////////////////////////////////////////////////////////////////////////////
// INPUT:
// (1) <m> x <m> matrix
// (2) integer <n>
// OUTPUT: matrix inserted at the top left of <n> x <n> matrix
MyInsertBlock := function(block, n)
  local f, mat;
  f := BaseRing(block);
  mat := IdentityMatrix(f,n);
  InsertBlock(~mat,block,1,1);
  return mat;
end function;

/*
InsertBlock := function(block, n)
local  m, f, zrow, bas, top;
   m := #block;
   f := Field(block[1][1]);
   zrow := List([1..n-m], i->Zero(f));
   bas := Basis( f^n );
   top := List( block, x->Concatenation(x, zrow) );
return Concatenation(top, bas{[m+1..n]});
end function;
*/

// writes a nonnegative integer <n> < <p>^<e> in base <p>
NtoPadic := function(p, e, n)
local  j, output; 
   output := [];
   for j in [1..e] do
      //output[j] := (n mod p)*Z(p)^0;
      output[j] := GF(p)!n;
      //n := ( n - (n mod p) ) div p;
      n := n div p;
   end for;
return VectorSpace(GF(p),e)!output;
end function;

// writes a vector in GF(<p>)^<e> as a nonnegative integer 
PadictoN := function(p, e, vector)
local  j, output; 
   output := 0;
   for j in [1..e] do
      output := output + p^(j-1)*Integers()!vector[j];
   end for;
return output;
end function;

// computes the 2-part of <n>
twopart := function(n)
local  k, m;
   k := 0;
   m := n;
   while m mod 2 eq 0 do
      m := m div 2;
      k := k + 1;
   end while;
return [k,m];
end function;
