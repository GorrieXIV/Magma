freeze;

/* Define the exceptional graph automorphism of Sp(4,2^n)
 * and the triality automorphism of O^+(8,q)
 */

GAutSp := function(q)
  local fac, e, K, X, w, diag, gens, imgens, G, evalim, nu;
  fac := Factorisation(q);
  assert fac[1][1] eq 2 and q gt 2;
  e := fac[1][2];
  K := GF(q);
  X := GL(4,q);
  w := PrimitiveElement(K);
  diag := [<i,i,1> : i in [1..4]];
  //make Chevalley generators of Sp(4,q)
  gens := [
  X!Matrix(K,4,4,diag cat [<1,2,w>, <3,4,-w>]),  //a
  X!Matrix(K,4,4,diag cat [<4,3,-w>, <2,1,w>]),  //-a
  X!Matrix(K,4,4,diag cat [<1,3,w>, <2,4,w>]), //a+b
  X!Matrix(K,4,4,diag cat [<4,2,w>, <3,1,w>]),//-a-b
  X!Matrix(K,4,4,diag cat [<1,4,w>]), //2a+b
  X!Matrix(K,4,4,diag cat [<4,1,w>]), //-2a-b
  X!Matrix(K,4,4,diag cat [<2,3,w>]), //b
  X!Matrix(K,4,4,diag cat [<3,2,w>]) //-b
  ];

  //images under graph automorphism (q even)
  imgens := [
  X!Matrix(K,4,4,diag cat [<2,3,w^2>]), //b
  X!Matrix(K,4,4,diag cat [<3,2,w^2>]), //-b
  X!Matrix(K,4,4,diag cat [<1,4,w^2>]), //2a+b
  X!Matrix(K,4,4,diag cat [<4,1,w^2>]), //-2a-b
  X!Matrix(K,4,4,diag cat [<1,3,w>, <2,4,w>]), //a+b
  X!Matrix(K,4,4,diag cat [<4,2,w>, <3,1,w>]),//-a-b
  X!Matrix(K,4,4,diag cat [<1,2,w>, <3,4,-w>]),  //a
  X!Matrix(K,4,4,diag cat [<4,3,-w>, <2,1,w>])  //-a
  ];

  G := sub< X | gens >;
  T := CompositionTree(G);
  nu := CompositionTreeNiceToUser(G);
  evalim := function(g) //evaluate outer automorphism on g
    local flag, wd;
    flag, wd := CompositionTreeElementToWord(G,g); assert flag;
    return Evaluate(nu(wd), imgens);
  end function;

  return evalim;
end function;

GAutO8Plus := function(q)
  local fac, p, e, K, w, I, E, i, j, gens, imgens, G, evalim, nu;
  fac := Factorisation(q);
  p :=fac[1][1]; e := fac[1][2];
  K := GF(q);
  w := PrimitiveElement(K);
  I := IdentityMatrix(K,8);
  E := function(i,j)
    local M;
    M:=I;
    if i lt 0 then i +:= 9; end if;
    if j lt 0 then j +:= 9; end if;
    M[i][j] := K!1;
    return(M);
  end function;
/* EE:=function(i,j,t)
     return I + t * ( E(i,j)-E(-j,-i) );
   end function; */
  gens := [];
  for i in [1..3] do for j in [i+1..4] do
    Append(~gens, I + w * ( E(i,j)-E(-j,-i) ) ); 
    Append(~gens, I + w * ( E(-i,-j)-E(j,i) ) ); 
    Append(~gens, I + w * ( E(i,-j)-E(j,-i) ) ); 
    Append(~gens, I + w * ( E(-i,j)-E(-j,i) ) ); 
  end for; end for;
  imgens := [];
  i:=3; j:=4;
  Append(~imgens, I + w * ( E(i,j)-E(-j,-i) ) ); 
  Append(~imgens, I + w * ( E(-i,-j)-E(j,i) ) ); 
  i:=1; j:=2;
  Append(~imgens, I + w * ( E(i,-j)-E(j,-i) ) ); 
  Append(~imgens, I + w * ( E(-i,j)-E(-j,i) ) ); 
  i:=2; j:=4;
  Append(~imgens, I - w * ( E(i,j)-E(-j,-i) ) ); 
  Append(~imgens, I - w * ( E(-i,-j)-E(j,i) ) ); 
  i:=1; j:=3;
  Append(~imgens, I + w * ( E(i,-j)-E(j,-i) ) ); 
  Append(~imgens, I + w * ( E(-i,j)-E(-j,i) ) ); 
  i:=2; j:=3;
  Append(~imgens, I + w * ( E(i,-j)-E(j,-i) ) ); 
  Append(~imgens, I + w * ( E(-i,j)-E(-j,i) ) ); 
  i:=1; j:=4;
  Append(~imgens, I + w * ( E(i,j)-E(-j,-i) ) ); 
  Append(~imgens, I + w * ( E(-i,-j)-E(j,i) ) ); 
  i:=2; j:=3;
  Append(~imgens, I + w * ( E(i,j)-E(-j,-i) ) ); 
  Append(~imgens, I + w * ( E(-i,-j)-E(j,i) ) ); 
  i:=1; j:=4;
  Append(~imgens, I + w * ( E(i,-j)-E(j,-i) ) ); 
  Append(~imgens, I + w * ( E(-i,j)-E(-j,i) ) ); 
  i:=2; j:=4;
  Append(~imgens, I + w * ( E(i,-j)-E(j,-i) ) ); 
  Append(~imgens, I + w * ( E(-i,j)-E(-j,i) ) ); 
  i:=1; j:=3;
  Append(~imgens, I - w * ( E(i,j)-E(-j,-i) ) ); 
  Append(~imgens, I - w * ( E(-i,-j)-E(j,i) ) ); 
  i:=3; j:=4;
  Append(~imgens, I + w * ( E(i,-j)-E(j,-i) ) ); 
  Append(~imgens, I + w * ( E(-i,j)-E(-j,i) ) ); 
  i:=1; j:=2;
  Append(~imgens, I + w * ( E(i,j)-E(-j,-i) ) ); 
  Append(~imgens, I + w * ( E(-i,-j)-E(j,i) ) ); 

  G := sub< GL(8,q) | gens >;
  ChangeUniverse( ~imgens, GL(8,q) );
  T := CompositionTree(G);
  nu := CompositionTreeNiceToUser(G);
  evalim := function(g) //evaluate outer automorphism on g
    local flag, wd;
    flag, wd := CompositionTreeElementToWord(G,Generic(G)!g); assert flag;
    return Evaluate(nu(wd), imgens);
  end function;

  return evalim;
end function;
