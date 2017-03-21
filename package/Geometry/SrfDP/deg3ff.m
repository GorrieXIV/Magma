freeze;

/************************************************************************ 
Routines for cubic surfaces over finite fields 

Intrinsics:

NumberOfPointsOnCubicSurface
  Point-count based on Lefschetz trace formula

IsIsomorphicCubicSurface
  Testing isomorphy using pentahedra or the 27 lines

Stephan Elsenhans, March 2011

************************************************************************/

declare verbose CubicSurface,2;

IsSmoothSurface := function(gl) 
 local c_r, chart, s_loc, subs, akt;

 c_r := PolynomialRing(FieldOfFractions(BaseRing(Parent(gl))),3);

 subs :=  [[1, c_r.1, c_r.2, c_r.3],  [c_r.1, 1, c_r.2, c_r.3],  
           [c_r.1, c_r.2, 1, c_r.3],  [c_r.1, c_r.2, c_r.3, 1]];

 for akt in subs do
  chart := Evaluate(gl, akt);
  s_loc := ideal<c_r | chart, Derivative(chart,1), 
                      Derivative(chart,2),Derivative(chart,3)>; 
  if s_loc ne ideal<c_r | 1> then
   return false;
  end if; 
 end for;
 return true;
end function;

/* Gives us all lines on a cubic surface.
   In general 6 charts have to be used. The lines are decomposed into Galois-Orbits.
   (Note: this duplicates LinesInScheme)
*/
LinesChartSubs := function(a1,a2,a3,a4, i)
 assert i in [1..6]; /* Only 6 charts available */
 return  [ [[1,0,a1, a2], [0,1,a3, a4]], [[1,a1,0, a2], [0,0,1,a3] ], 
           [[1,a1,a2,0],  [0,0,0,1]],    [[0,1,0,a1], [0,0,1, a2]], 
           [[0,1,a1,0], [0,0,0,1]],      [[0,0,1,0], [0,0,0,1]] ][i];
end function;

ChartsOfLines := function(f)
 local r, a4, charts,i, ind, orb, gr;

 r := Parent(f);
/* if Characteristic(BaseRing(r)) eq 2 then ind := [0,1,BaseRing(r).1]; else ind := [0,1,2]; end if; */
 ind := [0,1]; 
 gr := [Derivative(f,i) : i in [1..4]];
 charts := [ideal<r | [Evaluate(f,[1,i,r.1+i*r.3, r.2+i*r.4]) : i in ind] cat 
                      [Evaluate(f,[0,1,r.3,r.4]), &+[Evaluate(gr[i],[1,0,r.1,r.2]) * [0,1,r.3,r.4][i] : i in [1..4]]]>, 
            ideal<r | [Evaluate(f,[1,r.1,i, r.2+i*r.3]) : i in ind] cat 
                      [Evaluate(f,[0,0,1,r.3]), r.4,  &+[Evaluate(gr[i],[1,r.1,0,r.2]) * [0,0,1,r.3][i] : i in [1..4]]]>,
            ideal<r | [Evaluate(f,[1,r.1,r.2, i]) : i in ind] cat 
                      [Evaluate(f,[0,0,0,1]), r.3, r.4, Evaluate(gr[4],[1,r.1,r.2,0]) ]>, 

            ideal<r | [Evaluate(f,[0,1,i,r.1 + r.2*i]) : i in ind] cat 
                      [Evaluate(f,[0,0,1,r.2]), r.3, r.4, &+[Evaluate(gr[i],[0,1,0,r.1]) * [0,0,1,r.2][i] : i in [1..4]]]>,
            ideal<r | [Evaluate(f,[0,1,r.1,i]) : i in ind] cat 
                      [Evaluate(f,[0,0,0,1]), r.2, r.3, r.4, Evaluate(gr[4],[0,1,r.1,0])]>, 

            ideal<r | [Evaluate(f,[0,0,1,i]) : i in ind] cat 
                      [Evaluate(f,[0,0,0,1]), r.1, r.2, r.3, r.4, Evaluate(gr[4],[0,0,1,0])]> ];

 orb := [PrimaryDecomposition(Radical(i)) : i in charts];
 return orb;
end function;
 

/* For each line a pair of points is returned. The order of the lines gives the operation of Frobenius */
LinesOverExtension := function(lc, f_q, f_qe)
 local a4, gp, ca,S, pts, i, j,k, p0, orb, len, subs, r4, cz;

 a4 := AffineSpace(f_qe,4); 
 gp := [];
 r4 := PolynomialRing(f_qe,4);
/*  subs := [ [[1,0,r4.1, r4.2], [0,1,r4.3, r4.4]], [[1,r4.1,0, r4.2], [0,0,1,r4.3] ], 
           [[1,r4.1,r4.2,0],  [0,0,0,1]],        [[0,1,0,r4.1], [0,0,1,r4.2]], 
           [[0,1,r4.1,0], [0,0,0,1]],            [[0,0,1,0], [0,0,0,1]] ]; */

 for cz := 1 to 6 do 
  subs := LinesChartSubs(r4.1,r4.2,r4.3,r4.4,cz);
  for i := 1 to #lc[cz] do
   if not (1 in lc[cz][i])  then
    S := Scheme(a4,Basis(lc[cz][i]));
    pts := Points(S);
    p0 := pts[1];
    p0 := [p0[j] : j in [1..4]]; 
/* We use the Frobenius to order the lines if the basefield is finite */
    if IsFinite(f_qe) then
     orb := p0;
     len := 0;
     repeat
      len := len + 1;
      Append(~gp, [[Evaluate(subs[k][j],orb) : j in [1..4]] : k in [1..2]]);
      orb := [Frobenius(orb[j],f_q) : j in [1..4]];
     until orb eq p0;
     assert len eq #pts; /* Ideal was not prime */ 
    else
     gp := gp cat [[p0[j] : j in [1..4]] : p0 in pts];
    end if;
   end if; 
  end for;
 end for;
 return gp;
end function;
 

intrinsic NumberOfPointsOnCubicSurface(f :: RngMPolElt) -> RngIntElt, RngIntElt
{Count points of a smooth cubic surface over a finite field by inspecting the Galois-action on the 27 lines.
 The second return value is the Swinnerton-Dyer number of the Frobenius.}

 require ((Rank(Parent(f)) eq 4) and IsFinite(BaseRing(Parent(f)))
          and IsField(BaseRing(Parent(f)))): 
  "Polynomial with 4 varialbles over a finite Field expected."; 
 
 require ({Degree(akt) : akt in Monomials(f)} eq {3}):  
  "Homogenous cubic polynomial expected.";

 require IsSmoothSurface(f): 
  "Singular surfaces can not be handled.";

 q := #BaseRing(Parent(f));

 vprintf CubicSurface,1:"Searching for lines.\n";
 lc := ChartsOfLines(f);

 deg_list := [QuotientDimension(id) : id in (&cat lc) | not (1 in id)];

 vprintf CubicSurface,1:"Analyzing Frobenius orbit lengths of the lines.\n";
 sdl := Sort(deg_list);

 vprintf CubicSurface,1:"Orbit lenghts %o found.\n",sdl;  
 i := Index([[ 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1 ],
             [ 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 2, 2, 2, 2, 2, 2 ],
             [ 1, 1, 1, 1, 1, 1, 1, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2 ],
             [ 1, 1, 1, 1, 1, 1, 1, 1, 1, 3, 3, 3, 3, 3, 3 ],
             [ 1, 1, 1, 4, 4, 4, 4, 4, 4 ], [ 1, 1, 1, 1, 1, 2, 4, 4, 4, 4, 4 ],
             [ 1, 1, 5, 5, 5, 5, 5 ], [ 3, 3, 3, 3, 3, 6, 6 ],
             [ 1, 1, 1, 2, 2, 2, 6, 6, 6 ], [ 1, 1, 1, 2, 2, 2, 3, 3, 3, 3, 6 ],
             [ 1, 2, 2, 2, 2, 3, 3, 6, 6 ], [ 1, 2, 8, 8, 8 ], [ 9, 9, 9 ],
             [ 2, 5, 5, 5, 10 ], [ 3, 12, 12 ], [ 1, 4, 4, 6, 12 ]], sdl);
/* printf"Case A%o\n",i; */
 if i gt 0 then 
  trace :=  [ 6,  4, 2, 3, 2,  2,  1, -2, 1,  1, -1,  0,  0, -1, -1, 1 ][i];
  sd_num := [ 1, 16, 2, 6, 4, 18, 15, 22, 7, 21,  8, 20, 14, 25, 13, 24][i];
  return(q^2 + q + 1 + q * trace), sd_num; 
 end if; 

 assert sdl in  [[ 1, 2, 2, 2, 4, 4, 4, 4, 4 ], [ 3, 6, 6, 6, 6 ], [ 3, 3, 3, 3, 3, 3, 3, 3, 3 ],    
                      [ 1, 1, 1, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2 ]];
/* Only these Factorization-Patterns remain. */

/* We have to inspect the intersection matrix */
 
 vprintf CubicSurface,1:"Analyzing Frobenius orbit lengths of the tritangent planes.\n";
 gp := LinesOverExtension(lc,GF(q),GF(q^LCM(deg_list)));
 assert #gp eq 27; // not 27 lines found 
 ism := ZeroMatrix(IntegerRing(),27,27);
 for i := 1 to 26 do
  for j := i+1 to 27 do
   r := Rank(Matrix(gp[i] cat gp[j]));
   if r eq 3 then
    ism[i,j] := 1; ism[j,i] := 1; 
   end if;
   assert r ge 3; // "Error lines are not pairwise different"
  end for;
 end for; 
 for i := 1 to 27 do ism[i,i] := -1; end for;

 triangles := {{i,j,k} : i,j,k in [1..27] | (ism[i,j] eq 1) and (ism[i,k] eq 1) and (ism[j,k] eq 1)};

 assert #triangles eq 45; // Exactly 45 triangles are there 

/* Frobenius action on the lines i-th line is maped to frob_list[i]-th line */
 frob_list := [];
 for i := 1 to #deg_list do
  for j := 1 to deg_list[i]-1 do
   Append(~frob_list,#frob_list+2); 
  end for;
  Append(~frob_list,#frob_list+2-deg_list[i]);
 end for;

 frob := PermutationGroup<27 | Sym(27)!frob_list>;
 orb_45 := Orbits(frob,GSet(frob,triangles));    
 l_45 := [#i : i in orb_45]; 
 Sort(~l_45); 
 vprintf CubicSurface,1:"Orbit lenghts %o found.\n",l_45;
 i := Index([[ 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2 ],
             [ 1, 1, 1, 1, 1, 1, 1, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2 ],
             [ 1, 1, 1, 1, 1, 1, 1, 1, 1, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3 ],
             [ 1, 1, 1, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3 ],
             [ 1, 1, 1, 2, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4 ],
             [ 1, 2, 2, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4 ],
             [ 1, 2, 2, 2, 2, 3, 3, 3, 3, 6, 6, 6, 6 ],
             [ 1, 2, 3, 3, 3, 3, 6, 6, 6, 6, 6 ],
             [ 1, 2, 3, 3, 6, 6, 6, 6, 6, 6 ]], l_45);
/* printf "Case B%o\n",i; */
 assert (i gt 0); /* Impossible Galois action */
 trace := [ -2,  0, -3, 0, -2, 0,  1, -2,  0][i];
 sd_num := [ 3, 17, 11, 9, 19, 5, 12, 10, 23][i];
 return(q^2+q+1+q*trace), sd_num;
end intrinsic;

/* Code for isomorphy testing */

IsIsomorphismOfCubicSurfaces := function(f,g,mat)
 local i,j, r, tmp, subs, r4, qu;

 r4 := PolynomialRing(BaseRing(Parent(mat)),4);
 tmp := (r4!g)^mat;
 if Monomials(tmp) ne Monomials(r4!f) then
  return false;
 end if; 
 qu := {MonomialCoefficient(tmp,i) / MonomialCoefficient(r4!f,i) : i in Monomials(r4!f)};
 return #qu eq 1;
end function;

/* Given 2 finite Pointsets in P^n. 
   This routine will search for all linear isomorphisms between them. 
   Return values
    1st : true if test can be done (Points have to be in general position)
    2nd : list of matrices.
*/

FivePointsInGeneralPosition := function(pl)
 local i1,i2,i3,i4,i5,r3,r4,r5, i, min;

 for i1 := 1 to #pl - 4 do
  for i2 := i1 + 1 to #pl - 3 do
   r3 := [ i : i in [i2+1..#pl-2] | not ({0} eq Set(Minors(Matrix([pl[i1], pl[i2],pl[i]]),3)))];
   for i3 in r3 do
    r4 := [ i : i in [i3+1..#pl-1] | not (0 eq Determinant(Matrix([pl[i1], pl[i2],pl[i3],pl[i]])))];
    for i4 in r4 do
     for i5 in r4 do
      min := Minors(Matrix([pl[i1],pl[i2],pl[i3],pl[i4],pl[i5]]),4);
      if not 0 in min  then 
       return true,[i1,i2,i3,i4,i5];
      end if;
     end for;
    end for;
   end for;
  end for;
 end for; 
 return false,[];
end function;

/* given 5 points in P^3 in general position. This routine will give a matrix that
   transforms them to [*,0,0,0], [0,*,0,0], [0,0,*,0], [0,0,0,*], [1,1,1,1] */
Tran5Pt := function(pl)
 local mat1,mat2,sol,i,j, inv;

 mat1 := Matrix([pl[i] : i in [1..4]]);
 mat2 := mat1^(-1); 
 sol :=  [&+[mat2[j,i] * pl[5][j] : j in [1..4]] : i in [1..4]];
 for i := 1 to 4 do 
  inv := 1 / sol[i];
  for j := 1 to 4 do 
   mat2[j,i] := mat2[j,i] * inv; 
  end for; 
 end for;  
 return mat2;
end function; 

IsomorphismsOfPointSets := function(spf, spg)
 local mat2, mat4, mat6,i,j,k, rf, rg, ind_f, suc, spf_norm, res,
       pt, i1,i2,i3,i4,i5, spg_norm, lines, planes, r4, r5, inv;

/* spf; spg;    */
 rf := Rank(Matrix(spf)); 
 rg := Rank(Matrix(spg));

 if rf ne rg then  return true,[]; end if;
 if rf lt #(spf[1]) then return false,[];  end if;

 suc, ind_f := FivePointsInGeneralPosition(spf);
 if not suc then
  return false,[];
 end if;
 
/* Transform these points to [1,0,0,0], [0,1,0,0], [0,0,1,0], [0,0,0,1], [1,1,1,1] */
 mat2 := Tran5Pt([spf[ind_f[i]] : i in [1..5]]);
 
 spf_norm := [[&+[pt[i] *  mat2[i,j] : i in [1..4]] : j in [1..4]] : pt in spf]; 
 for i := 1 to #spf_norm do
  j := 1; while spf_norm[i][j] eq 0 do j := j + 1; end while;
  spf_norm[i] := [spf_norm[i][k] / spf_norm[i][j] : k in [1..4]];
 end for;
 spf_norm := Set(spf_norm);
 res := [];

/* Compute lines and planes of the pentahder only once */
 lines := {i : i in Subsets({1..#spg},3)  | Rank(Matrix([spg[j] : j in i])) lt 3};
 planes := {i : i in  Subsets({1..#spg},4) | Rank(Matrix([spg[j] : j in i])) lt 4};
 for i1 := 1 to #spg do 
  for i2 := 1 to #spg do
   for i3 := 1 to #spg do
    if not {i1,i2,i3} in lines then
     r4 := [i4 : i4 in [1..#spg] | not ({i1,i2,i4} in lines or {i1,i2,i4} in lines or 
                                        {i1,i3,i4} in lines or {i2,i3,i4} in lines)];
     r4 := [i4 : i4 in r4 | (not {i1,i2,i3,i4} in planes) and #{i1,i2,i3,i4} eq 4];
     for i4 in r4 do
      r5 := [i5 : i5 in r4 | not ({i1,i2,i3,i5} in planes or {i1,i2,i4,i5} in planes or 
                                  {i1,i3,i4,i5} in planes or {i2,i3,i4,i5} in planes) 
                            and not i5 in {i1,i2,i3,i4}];
      for i5 in r5 do
       mat4 := Tran5Pt([spg[i1], spg[i2],spg[i3],spg[i4],spg[i5]]);
       suc := true;
       i := 0;
       repeat  /* Test remaining points */
        i := i + 1;
        if not i in [i1,i2,i3,i4,i5] then
         spg_norm := [&+[spg[i][j] *  mat4[j,k] : j in [1..4]] : k in [1..4]];
         j := 1; while spg_norm[j] eq 0 do j := j + 1; end while;
         inv := 1 /  spg_norm[j];
         spg_norm := [spg_norm[k] * inv : k in [1..4]];
         suc := spg_norm in spf_norm; 
        end if;
       until (not suc) or (i eq #spg);
       if suc then
        mat6 := mat2 * mat4^(-1);
        i := 1; while mat6[1,i] eq 0 do i := i + 1; end while;
        Append(~res,Transpose((1/mat6[1,i])*mat6));
       end if;
      end for; 
     end for; 
    end if; 
   end for; 
  end for; 
 end for;

 return true,res;
end function;


/* Return values 
   1st  Could we test?
   2nd  Result of test (if 1st is true)
   3rd  Isomorphisms (if 1st and 2nd are true)
*/
IsomorphismsBySingularitiesOfHessian := function(f,g)
 local r,p3, hf, hg, i,j, sing_hf, sing_hg, cf,cg, spf, spg, ml, suc;

 vprintf CubicSurface,1:"Trying to use the pentahedron\n";

 hf := Determinant(Matrix([[Derivative(Derivative(f,i),j) : i in [1..4]] : j in [1..4]]));
 hg := Determinant(Matrix([[Derivative(Derivative(g,i),j) : i in [1..4]] : j in [1..4]]));

 r := BaseRing(Parent(f));

 p3 := ProjectiveSpace(r,3);
 sing_hf := Scheme(p3, [hf] cat [Derivative(hf,i) : i in [1..4]]); 
 sing_hg := Scheme(p3, [hg] cat [Derivative(hg,i) : i in [1..4]]); 
 cf := IsCluster(sing_hf);
 cg := IsCluster(sing_hg);
 if cf xor cg then /* Only one hessian degenerates -- not isomorphic */
  return true, false,[];
 end if;
 if (not cf) or (not cg) then /* both hessian degenerate -- can not test in this way */
  vprintf CubicSurface,1:"Degenerated pentahedra\n"; 
  return false, false,[];
 end if; 
 spf := PointsOverSplittingField(sing_hf);
 spg := PointsOverSplittingField(sing_hg);

 if #spf ne #spg then
  return true, false,[];
 end if; 
 spf := [[i[j] : j in [1..4]] : i in spf];
 spg := [[i[j] : j in [1..4]] : i in spg];
 
 suc,ml := IsomorphismsOfPointSets(spf, spg);
 if not suc then
  vprintf CubicSurface,1:"Degenerated pentahedra\n"; 
  return false, false, [];
 end if;
 vprintf CubicSurface,1:"Checking candidates found\n"; 
/* Generically there are 120 maps between the pentaheders but not all of them are isomorphisms */
 ml := [i : i in ml | IsIsomorphismOfCubicSurfaces(f,g,i)];

 return true, #ml gt 0, ml;
end function;


/* s1 is a list of points in P^n that are known to lay on a line 
   This routine computes all Normalforms that of the pointset by moving 3 of them to [1,0], [1,1], [0,1]  
   
 If FirstOnly is set true, then only one normalization is returned.
*/
NormalizePointsOnLine := function(s1, FirstOnly)
 local i1,i2, i3, i,j, pr1, pr2, mat, res, nf, m1,m2,m3, pt;

 if Rank(Matrix(s1)) gt 2 then
  printf "Points are not on a line\n";
  s1;
  assert false;
 end if;

 i := 2; 
 while (Rank(Matrix([s1[1],s1[i]])) eq 1) and (i lt #s1) do
   i := i + 1;
 end while; 
 
 i1 := 1; 
 while s1[1][i1] eq 0 do i1 := i1 + 1; end while;
 i2 := 1;
 while s1[1][i1] * s1[i][i2] - s1[1][i2] * s1[i][i1]  eq 0 do i2 := i2 + 1; end while;
 pr1 := [[pt[i1],pt[i2]] : pt in s1]; /* We project to P^1 */

 res := [];
 for i1 := 1 to #pr1 do
  for i2 := 1 to #pr1 do
   if Rank(Matrix([pr1[i1],pr1[i2]])) eq 2 then
    mat := Matrix([pr1[i1],pr1[i2]])^(-1);
    pr2 := [[pt[1] * mat[1,1] + pt[2] * mat[2,1], pt[1] * mat[1,2] + pt[2] * mat[2,2]]  : pt in pr1];
    for i3 := 1 to #pr2 do
     if pr2[i3][1] ne 0 and pr2[i3][2] ne 0 then
      m1 := 1 / pr2[i3][1];
      m2 := 1 / pr2[i3][2];
      nf := [[pt[1] * m1, pt[2] * m2]  : pt in pr2];
      for i := 1 to #nf do
       if nf[i][1] ne 0 then m3 := 1 / nf[i][1]; else m3 := 1 / nf[i][2]; end if;
       nf[i] := [(nf[i][1] * m3) ,( nf[i][2] * m3)];
      end for;  
      Append(~res,Set(nf));
      if FirstOnly then return res; end if;
     end if;
    end for;
   end if;
  end for;
 end for;

 return res;
end function;


InersectionPointListList := function(gll) 
 local res,i,j,bm, ism;

 ism := ZeroMatrix(IntegerRing(),#gll,#gll);
 res := [[ [] : i in [1..#gll]] : j in [1..#gll]];
 for i := 1 to #gll-1 do
  for j := i+1 to #gll do
   bm := Kernel(Transpose(Matrix([gll[i][1],gll[i][2], gll[j][1], gll[j][2]])));
   if Dimension(bm) gt 1 then
    printf "Lines coincide\n";
   end if;
   if Dimension(bm) eq 1 then /* Only one intersection point */
    bm := BasisMatrix(bm);
    vec := [bm[1,k] : k in [1..4]];
    res[i][j] := vec; 
    res[j][i] := vec;     
    ism[i,j] := 1; ism[j,i] := 1; 
   end if;
  end for;
 end for;

 return res, ism; 
end function;

/* We test */
TestCompatibilityOfLines := function(ispt_f, ispt_g)
 local pl_f, pl_g, nfl_f, nfl_g, res, i,j,k;

 pl_f :=  [ [ispt_f[i][j] : j in [1..27] | #ispt_f[i][j] ge 1 ] : i in [1..27]];
 pl_g :=  [ [ispt_g[i][j] : j in [1..27] | #ispt_g[i][j] ge 1 ] : i in [1..27]];
 nfl_f := [NormalizePointsOnLine(pl_f[i],true) : i in [1..27]];  
 nfl_g := [NormalizePointsOnLine(pl_g[i],false) : i in [1..27]]; 

 res := ZeroMatrix(IntegerRing(),27,27);
 for i := 1 to 27 do
  k := 0;
  for j := 1 to 27 do
   if nfl_f[i][1] in nfl_g[j] then
    res[i,j] := 1;
    k := k + 1;
   end if;
  end for;
  if k eq 0 then
  /* printf "Incompatible line found\n"; */
   return false, res; 
  end if;
 end for;
 return true, res;
end function;



IsomorphismByLines := function(f,g)
 local lf,lg, deg_list, lines_f,lines_g, lines_eq_f, lines_eq_g, ispt_f, ispt_g, ism_f, ism_g, tri_f, tri_g, 
       eck_f, eck_g, eck_f2, eck_g2, l_comp, i,j, k, l, isg_f, isg_g, g_iso, g_aut, 
       iso, aut, a, gen5, tran_1, tran_2, pl, ind5, ind5_g, res, p1, p2, iter;
 
 vprintf CubicSurface,1:"Using 27 lines for the test\n"; 

 lf := ChartsOfLines(f);
 lg := ChartsOfLines(g);
 deg_list := [QuotientDimension(id) : id in (&cat lf) | not (1 in id)] cat 
             [QuotientDimension(id) : id in (&cat lg) | not (1 in id)];
 
 fq := BaseRing(Parent(f));
 fqe := GF((#fq)^LCM(deg_list));
 lines_f := LinesOverExtension(lf,fq,fqe); 
 lines_g := LinesOverExtension(lg,fq,fqe); 
 assert #lines_f eq 27; /* There are 27 lines. */
 assert #lines_g eq 27; /* There are 27 lines. */
/* There are 51840 isomorphisms of the intersection configuration of the lines.
   We do not want to test all of them.  */
 lines_eq_f := [ BasisMatrix(Kernel(Transpose(Matrix(lines_f[i])))) : i in [1..27]];
 lines_eq_g := [ BasisMatrix(Kernel(Transpose(Matrix(lines_g[i])))) : i in [1..27]];

 vprintf CubicSurface,1:"Computing intersection points\n";  
 ispt_f,ism_f := InersectionPointListList(lines_eq_f);
 ispt_g,ism_g := InersectionPointListList(lines_eq_g);
 
/* we search for Eckardt-points. If there are some, then this will radically cut down the number of 
   possibilites for automorphisms  */
 tri_f := [SetToSequence(i) : i in Subsets({1..27},3) | &and [1 eq ism_f[j,k] : j,k in i | j ne k ] ];
 tri_g := [SetToSequence(i) : i in Subsets({1..27},3) | &and [1 eq ism_g[j,k] : j,k in i | j ne k ] ];
 assert #tri_f eq 45; /* 45 tritangent planes */
 assert #tri_g eq 45; /* 45 tritangent planes */

 vprintf CubicSurface,1:"Searching for Eckardt-points\n";  
 eck_f := [i : i in tri_f | ispt_f[i[1]][i[2]] eq ispt_f[i[1]][i[3]] ];
 eck_f2 := &cat [ [ [i[1],i[2]], [i[1],i[3]], [i[2],i[3]] ] : i in eck_f];
 eck_g := [i : i in tri_g | ispt_g[i[1]][i[2]] eq ispt_g[i[1]][i[3]] ];
 eck_g2 := &cat [ [ [i[1],i[2]], [i[1],i[3]], [i[2],i[3]] ] : i in eck_g];

 if #eck_f ne #eck_g then
  return false,[];
 end if;

/* Check that lines are pairwise compatible */
 vprintf CubicSurface,1:"Testing pairwise compatibility of lines\n";   
 i,l_comp := TestCompatibilityOfLines(ispt_f,ispt_g);
 if not i then
  return false,[];
 end if;
/* l_comp; */

/* Select 5 of the intersection points in general position */
 vprintf CubicSurface,1:"Searching for 5 intersetion points in general position\n";  
 pl := [[i,j] : i,j in [1..27] | (i lt j) and ism_f[i,j] eq 1]; /* All intersection points */
 ind5 := [pl[1]];
 gen5 := [ ispt_f[ ind5[1][1] ][ ind5[1][2] ] ];
 i := 1;
 for j := 2 to 5 do
  i := i  + 1;
/*  printf "j = %o\n",j; */
  while (Rank(Matrix(gen5 cat [ispt_f[ pl[i][1] ][ pl[i][2] ]])) lt j and (j lt 5)) or 
        (0 in Minors(Matrix(gen5 cat [ispt_f[ pl[i][1] ][ pl[i][2] ]]) ,4) and (j eq 5))  do
   i := i + 1;
/*   printf "i = %o\n",i;  */
  end while;
  Append(~ind5, pl[i]);
  Append(~gen5, ispt_f[ ind5[j][1] ][ ind5[j][2] ]);
/*  gen5; */
 end for;  
 tran_1 := Tran5Pt(gen5);

 vprintf CubicSurface,1:"Computing combinatorial isomorphisms of line configuartion\n";   
 isg_f := Graph< {1..27} |  { {i,j} : i,j in [1..27] | ism_f[i,j] eq 1 }>;
 isg_g := Graph< {1..27} |  { {i,j} : i,j in [1..27] | ism_g[i,j] eq 1 }>;
 res,iso :=  IsIsomorphic(isg_f, isg_g); 
 iso := [Index(iso(i)) : i in [1..27]]; 
 assert res; /* Intersectiongraphs of lines on cubic surfaces are always the same. */
 g_aut := AutomorphismGroup(isg_g);
 res := [];
 iter := 0;
 for aut in g_aut do
  if l_comp[1,iso[1]^aut] eq 1 then 
   if &+[l_comp[i,iso[i]^aut] : i in [1..27]] eq 27 then
    vprintf CubicSurface,2:"Checking Eckardt points\n";   
    if {{ iso[i]^aut : i in a} :  a in  eck_f} eq {Set(a) : a in eck_g} then
/* map is compatible with line- and EckardtPoint-data */
/*    printf ".";*/
     vprintf CubicSurface,1:"Testing a candidate\n";   

     ind5_g := [ [ iso[i[1]]^aut, iso[i[2]]^aut ] : i in ind5 ];
     tran_2 := Tran5Pt([ ispt_g[i[1]][i[2]] : i in ind5_g ]);
     suc := true;
     for i := 1 to 27 do
      if suc then  
       for j := 1 to 27 do
        if ism_f[i,j] eq 1 then
         p1 := ispt_f[i][j];
         p1 := [ &+[tran_1[l,k] * p1[l] : l in [1..4]] : k in [1..4]];
         p2 := ispt_g[iso[i]^aut][iso[j]^aut];
         p2 := [ &+[tran_2[l,k] * p2[l] : l in [1..4]] : k in [1..4]];
         if Rank(Matrix([p1,p2])) gt 1 then
          suc := false;
         end if; 
        end if;
       end for;
      end if;
     end for;
     if suc then
      tran_2 :=  tran_1 * tran_2^(-1);
      i := 1;
      while tran_2[1,i] eq 0 do i := i + 1; end while;
      Append(~res,Transpose(tran_2 * (1/tran_2[1,i]))); 
     end if;
    end if;
   end if; 
  end if; 
 end for;

 return #res gt 0,res;
end function; 

/* Represent isomorphisms defined over the basefield of f by matrices over this field. */
TrySmallerField := function(ml,f)
 local i,j,k,r, res, in_smaller;
 
 r := BaseRing(Parent(f));
 res := [* *];
 for i := 1 to #ml do
  in_smaller := true;
  for j := 1 to 4 do
   for k := 1 to 4 do
    if not ml[i][j,k] in r then in_smaller := false; end if;
   end for;
  end for;
  if in_smaller then
   Append(~res,Matrix([[r!ml[i][j,k] : k in [1..4]] : j in [1..4]]));
  else
   Append(~res,ml[i]);
  end if;
 end for;

 return res;
end function;


intrinsic IsIsomorphicCubicSurface(f :: RngMPolElt, g :: RngMPolElt: UseLines := false) -> BoolElt, List
{Tests smooth cubic surfaces f and g if they are geometrically isomorphic.
The second returned value is a list of all isomorphisms, given as matrices.} 

 require Parent(f) eq Parent(g) : "Surfaces must be over the same ring.";

 require Rank(Parent(f)) eq 4 and Type(BaseRing(Parent(f))) eq FldFin: 
  "Polynomial with 4 variables over a finite field expected."; 

 require ({Degree(akt) : akt in Monomials(f) cat Monomials(g)} eq {3}):  
  "Homogenous cubic polynomial expected.";

 sf := IsSmoothSurface(f);
 sg := IsSmoothSurface(g);
 if sf xor sg then /* A smooth surface can not be isomorphic to a singular one */
  return false, [];
 end if;
 require sf and sg : "Surfaces are singular.";

 if not UseLines then
  suc,iso,mat_lst := IsomorphismsBySingularitiesOfHessian(f,g);
  if suc then 
   return iso, TrySmallerField(mat_lst,f);
  end if;
 end if;

 require IsFinite(BaseRing(Parent(f))) : "Infinite base field not yet implemented.";
 iso,mat_lst := IsomorphismByLines(f,g); 

 return iso, TrySmallerField(mat_lst,f);  
end intrinsic;


