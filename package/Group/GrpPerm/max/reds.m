freeze;
 
function Torus(d, p)
z:= PrimitiveElement(GF(p));
torus:= DiagonalMatrix([z, z^-1] cat [1 : i in [3..d]]);
return torus;
end function;

function Iden(d, p)
return Identity(GL(d, p));
end function;

/*
 * Throughout this file we make use of the fact that GL(d, p) 
 * is as described in Don's paper. 

/* 
 * Point meet hyperplane can be taken to be <(0, 0, \ldots, 1)> and
 * hyperplane is (0, a_1, \ldots, a_d-1).
 * that is matrices with (a)i1 = 0 for i > 1, (a)di = 0 for i < d.
 *
 */  
 
function SLPointMeetHyperplane(d, p)
  diag:= [<i,i,1>: i in [1..d]];
  z:= PrimitiveElement(GF(p));
  diag1:= DiagonalMatrix([z, z^-1] cat [1 : i in [3..d]]);
  diag2:= DiagonalMatrix([1 : i in [1..d-2]] cat [z, z^-1]);
  if d gt 3 then 
    sl1:= DiagonalJoin(<Iden(1, p), SL(d-2, p).1, Iden(1, p)>);
    sl2:= DiagonalJoin(<Iden(1, p), SL(d-2, p).2, Iden(1, p)>);
  else
    sl1:= Iden(d, p);
    sl2:= Iden(d, p);
  end if;
  transvec1:= GL(d, p)!Matrix(GF(p), d, d, [<1,2,1>] cat diag);
  transvec2:= GL(d, p)!Matrix(GF(p), d, d, [<d-1,d,1>] cat diag);
  return sub<SL(d, p)|diag1, diag2, sl1, sl2, transvec1, transvec2>;
end function;

/*
 * Point unmeet hyperplane can be taken to be <(1, 0, \ldots, 0)> 
 * and <(0, a_1, \ldots, a_d-1)>; first row is zero after 1st entry,
 * first column is zero after 1st entry.
 */
 
function SLPointUnmeetHyperplane(d, p)
  diag1:= Torus(d, p);
  sl1:= DiagonalJoin(Iden(1, p), SL(d-1, p).1);
  sl2:= DiagonalJoin(Iden(1, p), SL(d-1, p).2);
  return sub<SL(d, p)|diag1, sl1, sl2>; 
end function;

/*
 * point is (0, 0, \ldots, 1)
 */

function SLPointStab(d, p)
  z:= PrimitiveElement(GF(p));
  diag:= [<i,i,1>: i in [1..d]];
  grp:= SLPointMeetHyperplane(d, p);
  transvec:= GL(d, p)!Matrix(GF(p), d, d, diag cat [<2,1,1>]);
  return sub<SL(d, p)|grp, transvec>;
end function;    

/*
 * 
 */

function SLStabOfHalfDim(d, p)
  //this seems to be identical to SLStabOfNSpace(d,p,d/2)
  assert IsEven(d);
  half:= d div 2;
  diag:= [<i,i,1>: i in [1..d]];
  z:= PrimitiveElement(GF(p));
  diag1:= DiagonalMatrix([z] cat [1 : i in [2..d-1]] cat [z^-1]);
  dir_prod:= DirectProduct(SL(half, p), SL(half, p));
  transvec:= GL(d, p)!Matrix(GF(p), d, d, diag cat [<1, half+1, 1>]);
  return sub<SL(d, p)|diag1, dir_prod, transvec>;
end function;


 /*
 * We take the n-space to be (0, \ldots, 0, a_1, \ldots, a_n) and
 * the (d-n)-space to be (a_1, \ldots, a_d-n, 0, \ldots, 0)
 */

function SLStabOfNSpaceMissDual(d, p, n:general:=false)
  z:= PrimitiveElement(GF(p));
  diag1:= DiagonalMatrix([z] cat [1 : i in [2..d-1]] cat [z^-1]);
  diag2:= DiagonalMatrix([z] cat [1 : i in [2..d]] );
  dir_prod:= DirectProduct(SL(d-n, p), SL(n, p));
  if general then
    return sub<GL(d, p)|diag1, diag2, dir_prod>;
  end if;
  return sub<SL(d, p)|diag1, dir_prod>;
end function;

/*
 * We take the n-space to be (0, \ldots, 0, a_1, \ldots, a_n)
 */

function SLStabOfNSpace(d, p, n)
  diag:= [<i,i,1>: i in [1..d]];
  grp:= SLStabOfNSpaceMissDual(d, p, n);
  transvec:= GL(d, p)!Matrix(GF(p), d,d, [<1, d-n+1, 1>] cat diag);
  return sub<SL(d, p)|grp, transvec>;
end function;


function GLStabOfNSpace(d, p, n)
  diag:= [<i,i,1>: i in [1..d]];
  grp1:= DirectProduct(GL((d-n), p), GL(n, p));
  transvec:= GL(d, p)!Matrix(GF(p), d,d, [<1, d-n+1, 1>] cat diag);
  return sub<GL(d, p)|grp1, transvec>;
end function;

/*
 * We take the n-space to be (0, \ldots, 0, a_1, \ldots, a_n)
 * and the (d-n)-space to be (0, \ldots, 0, b_1, \ldots, b_(d-n))
 * 
 */

function SLStabOfNSpaceMeetDual(d, p, n : general:=false)
  lower:= Min({n, d-n});
  upper:= Max({n, d-n});
  assert not (lower eq upper);
  diag:= [<i,i,1>: i in [1..d]];
  z:= PrimitiveElement(GF(p));

  diag1:= GL(d, p)!Matrix(GF(p), d,d,
                [<1,1,z>,<lower+1,lower+1,z^-1>] cat [<i,i,1> : i in
		[2..lower] cat [lower+2..d]]);
  diag2:= GL(d, p)!Matrix(GF(p),d,d,
                [<1,1,z>,<d,d,z^-1>] cat [<i,i,1>: i in [2..d-1]]);
  diag3:= GL(d, p)!Matrix(GF(p),d,d,
                [<1,1,z>] cat [<i,i,1>: i in [2..d]]);

  prod1:= DirectProduct(SL(lower, p), SL(upper - lower, p));
  dir_prod:= DirectProduct(prod1, SL(d-upper, p));

  trans1:= GL(d, p)!Matrix(GF(p), d, d, diag cat [<1, lower+1, 1>]);
  trans2:= GL(d, p)!Matrix(GF(p), d, d, diag cat [<1, upper+1, 1>]); 
  trans3:= GL(d, p)!Matrix(GF(p), d, d, diag cat [<lower+1, upper+1, 1>]);
  if general then
    return sub<GL(d, p)|diag1, diag2, diag3, dir_prod, trans1, trans2, trans3>;
  end if;
  return sub<SL(d, p)|diag1, diag2, dir_prod, trans1, trans2, trans3>;
end function;

function ReduciblesSL(d, q: Novelties:=false, All:=true)
  assert d gt 1;
  list:= [];
  if Novelties then
    for i in [1 .. (d-1) div 2] do
      Append(~list,SLStabOfNSpaceMeetDual(d, q, i));
      Append(~list,SLStabOfNSpaceMissDual(d, q, i));
    end for;
  else
    lim := All select d-1 else d div 2;
    for i in [1..lim] do
      Append(~list, SLStabOfNSpace(d, q, i));
    end for;
  end if;
  return list;
end function;

