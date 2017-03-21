freeze;

//////////////////////////////////////////////////////////////////////
//
// Projective line over residue rings
//
// Markus Kirschmer, Oct 2012
//
// Currently supports fields, RngIntRes, F_q[t]/<f(t)> and RngOrdRes
//
// Note [SRD]: not public currently; the interface may need to change
//
//////////////////////////////////////////////////////////////////////

declare type ProjLine;

declare attributes ProjLine:
  Ring, BigRing, IsField, Size, V, Fact, Powers, Idempotents, Classes;

intrinsic Print(P::ProjLine)
{internal}
  require assigned(P`Ring) : "Invalid object";
  printf "Projective line over %m", P`Ring;
end intrinsic;

// intrinsic MyProjectiveLine(R::Rng : Vector:= true) -> ProjLine
// {Returns the projective line over the ring R}

function MyProjectiveLine(R : Vector:= true)
  T:= Type(R);
  if ISA(T, Fld) then
    P:= New(ProjLine);
    P`IsField:= true;
    P`Ring:= R;
    P`Size:= IsFinite(R) select #R+1 else 0;
  else
    if T eq RngIntRes then
      nrm:= func< x | x >;
      S:= Integers();
    elif T eq RngOrdRes then
      nrm:= func< x | Norm(x) >;
      S:= Order(Modulus(R));
    else
//    require T eq RngUPolRes: "Ring is not supported";
      S:= Parent(Modulus(R));
      k:= BaseRing(S);
//    require IsFinite(k) and IsField(k) : "Ring is not supported";
      nrm:= func< f | #k^Degree(f) >;
    end if;
    P:= New(ProjLine);
    P`Ring:= R;
    P`BigRing:= S;
    P`IsField:= false;
    M:= Modulus(R);
    P`Fact:= Factorization(M); 
    P`Powers:= [ f[1]^f[2]: f in P`Fact ];
    P`Size:= &*[ Integers() | (n+1) * n^(f[2]-1) where n:= nrm(f[1]) : f in P`Fact ];
    if #P`Fact gt 1 then
      P`Idempotents:= 
        T eq RngOrdRes select 
          [ P`Ring | a where _, a:= Idempotents(M div p, p): p in P`Powers]
        else
          [ P`Ring | a*m mod M where _, a:= XGCD(m, p) where m:= M div p : p in P`Powers];
    end if;
  end if;
  P`V:= Vector select RSpace(R, 2) else RMatrixSpace(R, 2, 1);
  return P;
end function;

intrinsic '#'(P::ProjLine) -> RngIntElt
{Returns the number of classes in the projective line P}
  return P`Size eq 0 select Infinity() else P`Size;
end intrinsic;

function norm(P, e)
  ok, e:= IsCoercible(P`V, e);
  if not ok then return false, _, _; end if;
  // in cases of matrices, we need ee[j] be an element not a vector...
  ee:= Eltseq(e);	
  
  if P`IsField then
    ok:= exists(j){ j: j in [1..2] | ee[j] ne 0 };
    if not ok then return false, _, _; end if;
    s:= ee[j];
  elif #P`Fact eq 0 then 
    return true, P`V ! [0,0], P`Ring ! 0;
  else
    ok, f:= CanChangeUniverse(ee, P`BigRing); assert ok;
    s:= [];
    for i in [1..#P`Powers] do
      ok:= exists(j){ j: j in [1..2] | f[j] mod P`Fact[i,1] ne 0 };
      if not ok then return false, _, _; end if;
      s[i]:= ee[j];
    end for;
    s:= #s eq 1 select s[1] else
        &+[ P`Idempotents[i] * s[i] : i in [1..#s] ];
  end if;

  return true, s^-1 * e, s; 
end function;

intrinsic Normalize(P::ProjLine, e::.) -> ModTupRngElt, RngElt
{Returns the canonical representative f of e in P and a scalar s such that e=s*f}
  ok, f, s:= norm(P, e);
  require ok : "Could not coerce e into P";
  return f, s;
end intrinsic;

// S=RngOrd, I=ideal in S. Get elements of S/I.
function reps(S, I)
  Q, h:= quo< StandardLattice(Degree(S)) | Matrix([ Eltseq(b) : b in Basis(I, S) ]) >;
  return Q, h;
end function;

procedure SetClasses(P)
  if assigned(P`Classes) then return; end if;
  error if P`Size eq 0, "Ring must be finite";

  if P`IsField then
    P`Classes := {@ P`V | [1,x] : x in P`Ring @} join {@ P`V | [0,1] @};
    return ;
  elif #P`Fact eq 0 then 
    P`Classes:= {@ P`V ! [0,0] @}; return;
  end if;

  ord:= Type(P`Ring) eq RngOrdRes;
  R:= P`Ring;
  S:= P`BigRing;
  PClasses:= [];
  n:= #P`Fact;
  for i in [1..n] do
    p:= P`Fact[i,1];
    if ord then
      pi:= WeakApproximation([P`Fact[i,1]: i in [1..n]], [i eq j select 1 else 0 : j in [1..n]]);
      Q, h:= reps(S, P`Powers[i]);
      l:= {@ P`V | [R | 1, Eltseq(x @@ h) ]: x in Q @};
      Q, h:= reps(S, P`Powers[i] div p);
      l join:= {@ P`V | [R | pi*(S ! Eltseq(x @@ h)), 1]: x in Q @};
    else 
      Q, h:= quo< S | P`Powers[i] >;
      l:= {@ P`V | [R | 1, x @@ h ]: x in Q @};
      Q, h:= quo< S | P`Powers[i] div p >;
      l join:= {@ P`V | [R | p*(x @@ h), 1]: x in Q @};
    end if;
    Append(~PClasses, l);
  end for;

  if n eq 1 then 
    P`Classes:= PClasses[1]; 
  else 
    CP:= CartesianProduct([ [1..#l]: l in PClasses ]);
    C:= {@ &+[ P`Idempotents[i] * PClasses[i,c[i]] : i in [1..n]]: c in CP @}; 
    P`Classes:= C; 
  end if;
end procedure;

intrinsic Classes(P::ProjLine) -> SetEnum
{The canonical representatives of the projective line P}
  SetClasses(P);
  return P`Classes;

  if #P`PClasses eq 1 then
    return P`PClasses[1];
  else
    n:= #P`Fact;
    L:= P`PClasses;
    CP:= CartesianProduct([ [1..#l]: l in L ]);
    C:= {@ &+[ P`Idempotents[i] * L[i,c[i]] : i in [1..n]]: c in CP @}; 
  end if;
  return C;
end intrinsic;

intrinsic IsCoercible(P::ProjLine, e::.) -> BoolElt, .
{Coerce e into the projective line P}
  if Type(e) eq RngIntElt then
    ok:= P`Size ne 0 and e gt 0 and e le P`Size;
    if ok then
      SetClasses(P);
      f:= P`Classes[e];
    end if;
  else
    ok, f:= norm(P, e);
  end if;
  if not ok then return false, "Illegal coercion"; end if;
  return true, f;
end intrinsic;

// intrinsic Index(P::ProjLine, e::.) -> RngIntElt
// {The index of e in the set of canonical representatives of the projective line P}

function PLIndex(P, e)
  ok, e:= norm(P, e);
//require ok : "Could not coerce e into P";
  SetClasses(P);
  idx:= Index( P`Classes, e );
  assert idx ne 0;
/* if #P`PClasses eq 1 then
    idx:= Index( P`PClasses[1], e );
    assert idx ne 0;
  else
    R:= Parent(Modulus(P`Ring));
    f:= [ R | e[1], e[2] ];
    idx:= 1; size:= 1;
    for i in [#P`PClasses..1 by -1] do
      p:= P`Powers[i];
      j:= Index( P`PClasses[i], [f[1] mod p, f[2] mod p] ); assert j ne 0;
      idx +:= (j-1) * size;
      size *:= #P`PClasses[i];
    end for;
  end if;*/
  return idx;
end function;
