freeze;



refTable := function( M )
mx := M;
counter:=0;
//
// mx should now be a Coxeter matrix
//
rank:=Degree(Parent(mx));
//
// The elementary roots will be placed in an indexed set, starting
// with the simple roots. Now act[j] will be a sequence whose i-th
// term describes the action of the j-th simple reflection on the
// i-th elementary root. If it takes the i-th elementary root to
// the k-th elementary root then act[j][i] = k . If it takes the
// i-th elementary root to a non-elementary root then act[j][i] = 0;
// if i = j (so that we are considering the action of a simple
// reflection on the corresponding simple root) then we define
// act[j][i] = -i.

// SH: if rank is 0, return [[Integers()|]], since the group has one generator.
// otherwise we'll get nasty null handle errors from C level...
    if rank eq 0 then
        return [[Integers()|]];
    end if;

act:=[];
for i in [1..rank] do
 act[i]:=[];
 act[i][i]:=-i;
end for;

eroots:={@ {@ <j,1> @} : j in [1..rank] @};
//
// An eroot will be an indexed set of sequences. The first term in
// each sequence is an integer between 1 and the rank, corresponding
// to a simple root in the support of the eroot. The other terms of
// the sequence describe the coefficient of that simple root. Indeed,
// if the 2nd, 3rd and 4th terms are a, b and m then the coefficient
// is a + 2b cos(pi/m). The 3rd and 4th terms are omitted if the
// coefficient is simply an integer.
// Thus {@ [j,1] @} is just the j-th simple root.
//
// It is in fact true that coefficients of the form a + 2b cos(pi/m)
// with a and b both nonzero occur only when m = 5.
//
// Elementary roots whose support just consists of two simple roots
// cannot always be represented in the form described above, since
// the coefficients are not always of the form a + 2b cos(pi/m).
// In fact, if the bond label is m then the two coefficients are
// s(q-1) and s(q), for some q in the interval from 2 to the integer
// part of (m-1)/2, where the definition of s(q) is
//             s(q) = sin(q(pi/m))/sin(pi/m).
// Coefficients of this form also occasionally occur in elementary
// roots whose support contains more than two simple roots, although
// then only when q = 3.
// We adopt the convention that [j,q-1,0,m] means s(q) times the
// the j-th simple root. Thus, for example, if simple roots 7 and 11
// are joined by a bond of weight 13 then
//          {@ [7, 5, 0, 13], [11, 4, 0, 13] @}
// occurs as an eroot.
//
// Note that [7, 2, 0, 6] and [7, 2] both indicate twice the 7th
// simple root, since sin(3(pi/6))/sin(pi/6) happens to equal 2.
//
// We start by explicitly writing down the elementary roots with
// two-element support.
//
C := CyclotomicField(LCM(Eltseq(2*mx))); z := C.1;
for i:=2 to rank do
 for j:=1 to i-1 do
  if mx[i][j] lt 0 then
   act[i][j]:=0;
   act[j][i]:=0;
  elif mx[i][j] eq 2 then
   act[i][j]:=j;
   act[j][i]:=i;
  elif mx[i][j] eq 3 then
   Include(~eroots, {@ <j,1>, <i,1> @});
   act[j][i]:=#eroots;
   act[i][j]:=#eroots;
   act[i][#eroots]:=j;
   act[j][#eroots]:=i;
  elif mx[i][j] eq 4 then
    root := RootOfUnity(2*4, C);
    rooti := root^-1;
   Include(~eroots, {@ <j,0+1*(root + rooti)>, <i,1> @});
   act[j][i]:=#eroots;
   act[j][#eroots]:=i;
   act[i][#eroots]:=#eroots;
   Include(~eroots, {@ <j,1>, <i,0+1*(root + rooti)> @});
   act[i][j]:=#eroots;
   act[i][#eroots]:=j;
   act[j][#eroots]:=#eroots;
  elif mx[i][j] eq 5 then
   root := RootOfUnity(2*5, C);
   rooti := root^-1;
   Include(~eroots, {@ <j,0+1*(root + rooti)>, <i,1> @});
   act[j][i]:=#eroots;
   act[j][#eroots]:=i;
   Include(~eroots, {@ <j,1>, <i,0+1*(root + rooti)> @});
   act[i][j]:=#eroots;
   act[i][#eroots]:=j;
   Include(~eroots, {@ <j,0+1*(root + rooti)>, <i,0+1*(root + rooti)> @});
   act[j][#eroots-1]:=#eroots;
   act[j][#eroots]:=#eroots-1;
   act[i][#eroots-2]:=#eroots;
   act[i][#eroots]:=#eroots-2;
  else
   root := RootOfUnity(2*mx[i, j], C);
   rooti := root^-1;
   Include(~eroots, {@ <j,0+1*(root + rooti)>, <i,1> @});
   act[j][i]:=#eroots;
   act[j][#eroots]:=i;
   Include(~eroots, {@ <j,1>, <i,0+1*(root + rooti)> @});
   act[i][j]:=#eroots;
   act[i][#eroots]:=j;
   Include(~eroots, {@ <j,(root^3 - rooti^3)/(root - rooti)<i,0+1*(root + rooti)> @});
   act[j][#eroots-1]:=#eroots;
   act[j][#eroots]:=#eroots-1;
   Include(~eroots, {@ <j,0+1*(root + rooti)>, <i,(root^3 - rooti^3)/(root - rooti)> @});
   act[i][#eroots-3]:=#eroots;
   act[i][#eroots]:=#eroots-3;
   ii:=3;
   while 2*ii lt mx[i][j] - 1 do
    Include(~eroots, {@ <j,(root^(ii+1) - rooti^(ii+1))/(root - rooti)>, <i,(root^ii - rooti^ii)/(root - rooti)> @});
    act[j][#eroots-1]:=#eroots;
    act[j][#eroots]:=#eroots-1;
    Include(~eroots, {@ <j,(root^ii - rooti^ii)/(root - rooti)>, <i,(root^(ii+1) - rooti^(ii+1))/(root - rooti)> @});
    act[i][#eroots-3]:=#eroots;
    act[i][#eroots]:=#eroots-3;
    ii +:= 1;
   end while;
   if IsOdd(mx[i][j]) then
    Include(~eroots, {@ <j,(root^(ii+1) - rooti^(ii+1))/(root - rooti)>, <i,(root^(ii+1) - rooti^(ii+1))/(root - rooti)> @});
    act[j][#eroots-1]:=#eroots;
    act[j][#eroots]:=#eroots-1;
    act[i][#eroots-2]:=#eroots;
    act[i][#eroots]:=#eroots-2;
   else
    act[j][#eroots]:=#eroots;
    act[i][#eroots-1]:=#eroots-1;
   end if;
  end if;
 end for;
end for;
//
// In the above calculations we have defined act[i][j] whenever
// i and j are less than or equal to the rank. We put i := rank
// and proceed to go through all values of k calculating act[k][i]
// (defining more eroots as required), and then augment i.
// We repeat this while i is not greater than #eroots.
//
i:=rank;
//
while i le #eroots do
 for k in [1..rank] do
//
// We work out what the k-th simple reflection does to the 
// eroots not considered yet.
//
  if IsDefined(act[k],i) then;
  else
   indk:=Index({@ ert[1] : ert in eroots[i] @},k);
// First we consider the case when the k-th simple root is not in the
// support of the eroot.
   if indk eq 0 then
    numjoins:=0;
    for f:=1 to #eroots[i] do
     if mx[k][eroots[i][f][1]] ne 2 then
      numjoins +:= 1;
// If there are 2 or more bonds, then there is a circuit created.
      if numjoins eq 2 then
       break;
      end if;
      x:=eroots[i][f][1];
      cfx:=eroots[i][f];
     end if;
    end for;
    if numjoins eq 0 then
     act[k][i]:=i;
    elif numjoins eq 2 then
     act[k][i]:=0;
    elif mx[k][x] lt 0 then
     act[k][i]:=0;
    elif cfx[2] ne 1 then
     if mx[k][x] ne 3 then
      act[k][i]:=0;
     elif cfx[2] ge 2 then
      act[k][i]:=0;
     elif #cfx gt 2 then
      if cfx[3] ge 2 then
       act[k][i]:=0;
      else
       cf:=cfx;
       cf[1]:=k;
       nextrt:=Include(eroots[i],cf);
       ind:=Index(eroots,nextrt);
       if ind eq 0 then
        Include(~eroots,nextrt);
        act[k][i]:=#eroots;
        act[k][#eroots]:=i;
       else
        act[k][i]:=ind;
        act[k][ind]:=i;
       end if;
      end if;
     else
      cf:=cfx;
      cf[1]:=k;
      nextrt:=Include(eroots[i],cf);
      ind:=Index(eroots,nextrt);
      if ind eq 0 then
       Include(~eroots,nextrt);
       act[k][i]:=#eroots;
       act[k][#eroots]:=i;
      else
       act[k][i]:=ind;
       act[k][ind]:=i;
      end if;
     end if;
    elif #cfx gt 2 then
      act[k][i]:=0;
    elif mx[k][x] eq 3 then
     nextrt:=Include(eroots[i],<k,1>);
     ind:=Index(eroots,nextrt);
     if ind eq 0 then
      Include(~eroots,nextrt);
      act[k][i]:=#eroots;
      act[k][#eroots]:=i;
     else
      act[k][i]:=ind;
      act[k][ind]:=i;
     end if;
    else
     root := RootOfUnity(2*mx[k, x], C);
     nextrt:=Include(eroots[i],<k,0+1*(root + root^-1)>);
     ind:=Index(eroots,nextrt);
     if ind eq 0 then
      Include(~eroots,nextrt);
      act[k][i]:=#eroots;
      act[k][#eroots]:=i;
     else
      act[k][i]:=ind;
      act[k][ind]:=i;
     end if;
    end if;
// Conclusion to the original if statement of this section. 
// Now we consider the case when the k-th simple root is in the support
// of the eroot.
   else
    nextrt:={@ cf : cf in eroots[i] | cf[1] ne k @};
    neighbours:={@ cf : cf in nextrt | mx[k][cf[1]] ne 2 @};
// First case, if the vertex corresponding to the k-th simple root in the support of 
// the eroot has degree greater than or equal to 4, then we are not dealing with 
// an elementary root.
    if #neighbours ge 4 then
     act[k][i]:=0;
// Secondly, we consider the case when the vertex corresponding to the
// k-th simple root in the support of the eroot has degree exactly equal to 3.
    elif #neighbours eq 3 then
     x:=neighbours[1][1];
     y:=neighbours[2][1];
     z:=neighbours[3][1];
     cfx:=neighbours[1];
     cfy:=neighbours[2];
     cfz:=neighbours[3];
     cfk:=eroots[i][indk];
// Here we consider the case when one of the bonds, that corresponding to the 
// edge between simple roots x and k, is not simple.
     if mx[k][x] gt 3 then
      if mx[k][y] gt 3 then
       act[k][i]:=0;
      elif mx[k][z] gt 3 then
       act[k][i]:=0;
// Hence the remaining cases deal with the situation where there are two simple
// bonds and one non- simple bond.
// There are two possible scenarios which now eventuate.
// Firstly, that the coefficient of the simple root x is an integer, and
// secondly that the coefficient of the simple root x is not an integer. 
// It turns out that if it is not an integer then the coefficient of the 
// k-th simple root must be 1. 
// Alternatively, if it is an integer this must mean that all the other coefficients in the 
// support are non- integers.  
// First case, with coefficient of the root x a non-integer, results in a non elementary root for
// the following reason.
// The coefficients of the y-th and z-th roots are each at least one, and similarly the 
// non-integer coefficient of x is at least one. Applying the reflection corresponding 
// to the simple root k is going to yield a new k-th coefficient which is the sum of the surrounding
// coefficients, minus the original coefficient, which, as stated above, was 1. Therefore
// the difference between the new and old coefficients of the k-th root is greater than or
// equal to two, yielding a non-elementary root.  
      elif #cfx gt 2 then
       act[k][i]:=0;
// We are left with the case that the coefficient of the x-th root is an integer.       
// Indeed, if the coefficient of the simple root x is not 1, then we do not
// have a elementary root.
      elif cfx[2] ne 1 then
       act[k][i]:=0;
// Since the remaining cases dictate that coefficient of the simple root x be 1, 
// Proposition 6.2 from Brink applies with l=1. As stated above, the coefficients of
// the y-th and z-th roots cannot be integers, and so the 3rd entries in their eroots
// sequence is defined. Proposition 6.2 states that there is a one-one correspondence to
// the case of strictly simple bonds, and so, the simple process of adding the coefficients
// of the surrounding roots and subtracting the coefficient of the k-th root yields the new k-th
// coefficient. If the difference between this new coefficient and the old one is greater than
// or equal to 2, then we do not have an elementary root.
      elif cfy[3]+cfz[3] ge 2*cfk[3] + 1 then
       act[k][i]:=0;
// If the difference between the new and old coefficients is zero, then the reflection changes
// nothing.
      elif cfy[3]+cfz[3]+1 eq 2*cfk[3] then
       act[k][i]:=i;
// Otherwise, there is a change in coefficient, and an allowable eroot.
      else
       cfk[3]:=cfy[3]+cfz[3]+1-cfk[3];
       Include(~nextrt,cfk);
       ind:=Index(eroots,nextrt);
       if ind eq 0 then
        Include(~eroots,nextrt);
        act[k][i]:=#eroots;
        act[k][#eroots]:=i;
       else
        act[k][i]:=ind;
        act[k][ind]:=i;
       end if;
      end if;
// This is the case where the bond between y and k is not simple.
     elif mx[k][y] gt 3 then
      if mx[k][z] gt 3 then
       act[k][i]:=0;
      elif #cfy gt 2 then
       act[k][i]:=0;
      elif cfy[2] ne 1 then
       act[k][i]:=0;
      elif cfx[3]+cfz[3] ge 2*cfk[3] + 1 then
       act[k][i]:=0;
      elif cfx[3]+cfz[3]+1 eq 2*cfk[3] then
       act[k][i]:=i;
      else
       cfk[3]:=cfx[3]+cfz[3]+1-cfk[3];
       Include(~nextrt,cfk);
       ind:=Index(eroots,nextrt);
       if ind eq 0 then
        Include(~eroots,nextrt);
        act[k][i]:=#eroots;
        act[k][#eroots]:=i;
       else
        act[k][i]:=ind;
        act[k][ind]:=i;
       end if;
      end if;
// This is the case where the bond between z and k is not simple.
     elif mx[k][z] gt 3 then
      if #cfz gt 2 then
       act[k][i]:=0;
      elif cfz[2] ne 1 then
       act[k][i]:=0;
      elif cfx[3]+cfy[3] ge 2*cfk[3] + 1 then

       act[k][i]:=0;
      elif cfx[3]+cfy[3]+1 eq 2*cfk[3] then
       act[k][i]:=i;
      else
       cfk[3]:=cfx[3]+cfy[3]+1-cfk[3];
       Include(~nextrt,cfk);
       ind:=Index(eroots,nextrt);
       if ind eq 0 then
        Include(~eroots,nextrt);
        act[k][i]:=#eroots;
        act[k][#eroots]:=i;
       else
        act[k][i]:=ind;
        act[k][ind]:=i;
       end if;
      end if;
// Here we consider the case where all the bonds incident with the
// k-th simple root are simple, and the coefficient of the k-th simple
// root is not an integer.
     elif #cfk gt 2 then
      if cfx[3]+cfy[3]+cfz[3] ge 2*cfk[3]+2 then
       act[k][i]:=0;
// To be elementary roots in this situation, all surrounding roots must have no
// integer part in the coefficient.(??)      
      elif cfx[2] ne 0 then
       act[k][i]:=0;
      elif cfy[2] ne 0 then
       act[k][i]:=0;
      elif cfz[2] ne 0 then
       act[k][i]:=0;
      elif cfx[3]+cfy[3]+cfz[3] eq 2*cfk[3] then
       act[k][i]:=i;
      else
       cfk[3]:=cfx[3]+cfy[3]+cfz[3]-cfk[3];
       Include(~nextrt,cfk);
       ind:=Index(eroots,nextrt);
       if ind eq 0 then
        Include(~eroots,nextrt);
        act[k][i]:=#eroots;
        act[k][#eroots]:=i;
       else
        act[k][i]:=ind;
        act[k][ind]:=i;
       end if;
      end if;
// Here we consider the cases where, with the coefficient of the k-th root an integer, 
// any of the 3 surrounding roots have non integer coefficients. Each one of these cases 
// yields a non elementary root.
     elif #cfx gt 2 then
       act[k][i]:=0;
     elif #cfy gt 2 then
       act[k][i]:=0;
     elif #cfz gt 2 then
       act[k][i]:=0;
// Here we consider the case where the coefficient of the roots x, y, z and k are all
// integers. Brink states that the only eroots of this form are if all coefficients
// are equal to 1, or if the coefficient of the k-th root is 2, and all others one.
     elif cfx[2]+cfy[2]+cfz[2] ge 2*cfk[2]+2 then
      act[k][i]:=0;
     elif cfx[2]+cfy[2]+cfz[2] eq 2*cfk[2] then
      act[k][i]:=i;
     else
      cfk[2]:=cfx[2]+cfy[2]+cfz[2]-cfk[2];
      Include(~nextrt,cfk);
      ind:=Index(eroots,nextrt);
      if ind eq 0 then
       Include(~eroots,nextrt);
       act[k][i]:=#eroots;
       act[k][#eroots]:=i;
      else
       act[k][i]:=ind;
       act[k][ind]:=i;
      end if;
     end if;
// Here we consider the case where the vertex of the k-th simple
// root in the support of the eroot has degree exactly equal to 2.    
    elif #neighbours eq 2 then
     x:=neighbours[1][1];
     y:=neighbours[2][1];
     cfx:=neighbours[1];
     cfy:=neighbours[2];
     cfk:=eroots[i][indk];
// The case where the bond between the k-th and the x-th simple roots is not
// simple.
     if mx[k][x] gt 3 then
      if mx[k][y] gt 3 then
       act[k][i]:=0;
// Following is the case when the coefficient of the k-th root is not an integer.
      elif #cfk gt 2 then
       if #cfy eq 2 then
        if cfx[2] eq 1 then
         act[k][i]:=i;
        else
         cfk:=<k,1>;
         Include(~nextrt,cfk);
         ind:=Index(eroots,nextrt);
         if ind eq 0 then
          Include(~eroots,nextrt);
          act[k][i]:=#eroots;
          act[k][#eroots]:=i;
         else
          act[k][i]:=ind;
          act[k][ind]:=i;
         end if;
        end if;
       elif #cfx eq 2 then
        if cfx[2] + cfy[3] eq 2*cfk[3] then
         act[k][i]:=i;
        elif cfx[2] + cfy[3] ge 2*cfk[3] + 2 then
         act[k][i]:=0;
        else
         cfk:=[k,0,cfx[2] + cfy[3] - cfk[3],cfk[4]];
         Include(~nextrt,cfk);
         ind:=Index(eroots,nextrt);
         if ind eq 0 then
          Include(~eroots,nextrt);
          act[k][i]:=#eroots;
          act[k][#eroots]:=i;
         else
          act[k][i]:=ind;
          act[k][ind]:=i;
         end if;
        end if;
       elif cfk[4] gt 6 then
        act[k][i]:=0;
       elif cfk[4] eq 6 then
        if cfy[3] eq 2 then
         act[k][i]:=i;
        else
         if cfk[3] eq 1 then
          cfk[3]:= 2;
         else
          cfk[3]:= 1;
         end if;
         Include(~nextrt,cfk);
         ind:=Index(eroots,nextrt);
         if ind eq 0 then
          Include(~eroots,nextrt);
          act[k][i]:=#eroots;
          act[k][#eroots]:=i;
         else
          act[k][i]:=ind;
          act[k][ind]:=i;
         end if;
        end if;
       else
        cc:=cfx[3] + cfy[2];
        ccc:=cfx[2] + cfx[3] + cfy[3];
        if (cc ge 2*cfk[2]+1) and (ccc ge 2*cfk[3] + 1) then
         act[k][i]:=0;
        elif (cc eq 2*cfk[2]) and (ccc eq 2*cfk[3]) then
         act[k][i]:=i;
        else
         cfk:=[k,cc-cfk[2],ccc-cfk[3],5];
         Include(~nextrt,cfk);
         ind:=Index(eroots,nextrt);
         if ind eq 0 then
          Include(~eroots,nextrt);
          act[k][i]:=#eroots;
          act[k][#eroots]:=i;
         else
          act[k][i]:=ind;
          act[k][ind]:=i;
         end if;
        end if;
       end if;
      elif mx[k][x] gt 5 then
       act[k][i]:=0;
      elif #cfy gt 2 then
       act[k][i]:=0;
      elif mx[k][x] eq 5 then
       if cfx[3] ne 1 then
        act[k][i]:=0;
       elif cfy[2] ne 1 then
        act[k][i]:=0;
       else
	root := RootOfUnity(2*5, C);
        cfk:=<k,1+1*(root + root^-1)>;
        Include(~nextrt,cfk);
        ind:=Index(eroots,nextrt);
        if ind eq 0 then
         Include(~eroots,nextrt);
         act[k][i]:=#eroots;
         act[k][#eroots]:=i;
        else
         act[k][i]:=ind;
         act[k][ind]:=i;
        end if;
       end if;
      else
       if 2*cfx[3]+cfy[2] ge 2*cfk[2]+2 then
        act[k][i]:=0;
       else
        cfk:=[k,2*cfx[3]+cfy[2]-cfk[2]];
        Include(~nextrt,cfk);
        ind:=Index(eroots,nextrt);
        if ind eq 0 then
         Include(~eroots,nextrt);
         act[k][i]:=#eroots;
         act[k][#eroots]:=i;
        else
         act[k][i]:=ind;
         act[k][ind]:=i;
        end if;
       end if;
      end if;
// The case where the bond between the k-th and y-th simple roots is not simple.
     elif mx[k][y] gt 3 then
// Firstly, the case when the coefficient of the k-th root is not an integer.      
      if #cfk gt 2 then
       if #cfx eq 2 then
        if cfy[2] eq 1 then
         act[k][i]:=i;
        else
         cfk:=<k,1>;
         Include(~nextrt,cfk);
         ind:=Index(eroots,nextrt);
         if ind eq 0 then
          Include(~eroots,nextrt);
          act[k][i]:=#eroots;
          act[k][#eroots]:=i;
         else
          act[k][i]:=ind;
          act[k][ind]:=i;
         end if;
        end if;
       elif #cfy eq 2 then
        if cfy[2] + cfx[3] eq 2*cfk[3] then
         act[k][i]:=i;
        elif cfy[2] + cfx[3] ge 2*cfk[3] + 2 then
         act[k][i]:=0;
        else
         cfk:=[k,0,cfy[2] + cfx[3] - cfk[3],cfk[4]];
         Include(~nextrt,cfk);
         ind:=Index(eroots,nextrt);
         if ind eq 0 then
          Include(~eroots,nextrt);
          act[k][i]:=#eroots;
          act[k][#eroots]:=i;
         else
          act[k][i]:=ind;
          act[k][ind]:=i;
         end if;
        end if;
       elif cfk[4] gt 6 then
        act[k][i]:=0;
       elif cfk[4] eq 6 then
        if cfx[3] eq 2 then
         act[k][i]:=i;
        else
         if cfk[3] eq 1 then
          cfk[3]:= 2;
         else
          cfk[3]:= 1;
         end if;
         Include(~nextrt,cfk);
         ind:=Index(eroots,nextrt);
         if ind eq 0 then
          Include(~eroots,nextrt);
          act[k][i]:=#eroots;
          act[k][#eroots]:=i;
         else
          act[k][i]:=ind;
          act[k][ind]:=i;
         end if;
        end if;
       else
        cc:=cfy[3] + cfx[2];
        ccc:=cfy[2] + cfy[3] + cfx[3];
        if (cc ge 2*cfk[2] + 1) and (ccc ge 2*cfk[3] + 1) then
         act[k][i]:=0;
        elif (cc eq 2*cfk[2]) and (ccc eq 2*cfk[3]) then
         act[k][i]:=i;
        else
         cfk:=[k,cfy[3]+cfx[2]-cfk[2],cfy[2]+cfy[3]+cfx[3]-cfk[3],5];
         Include(~nextrt,cfk);
         ind:=Index(eroots,nextrt);
         if ind eq 0 then
          Include(~eroots,nextrt);
          act[k][i]:=#eroots;
          act[k][#eroots]:=i;
         else
          act[k][i]:=ind;
          act[k][ind]:=i;
         end if;
        end if;
       end if;
      elif mx[k][y] gt 5 then
       act[k][i]:=0;
      elif #cfx gt 2 then
       act[k][i]:=0;
      elif mx[k][y] eq 5 then
       if cfy[3] ne 1 then
        act[k][i]:=0;
       elif cfx[2] ne 1 then
        act[k][i]:=0;
       else
	root := RootOfUnity(2*5, C);
        cfk:=<k,1+1*(root + root^-1)>;
        Include(~nextrt,cfk);
        ind:=Index(eroots,nextrt);
        if ind eq 0 then
         Include(~eroots,nextrt);
         act[k][i]:=#eroots;
         act[k][#eroots]:=i;
        else
         act[k][i]:=ind;
         act[k][ind]:=i;
        end if;
       end if;
      else
       if 2*cfy[3]+cfx[2] ge 2*cfk[2]+2 then
        act[k][i]:=0;
       else
        cfk:=[k,2*cfy[3]+cfx[2]-cfk[2]];
        Include(~nextrt,cfk);
        ind:=Index(eroots,nextrt);
        if ind eq 0 then
         Include(~eroots,nextrt);
         act[k][i]:=#eroots;
         act[k][#eroots]:=i;
        else
         act[k][i]:=ind;
         act[k][ind]:=i;
        end if;
       end if;
      end if;
// Here we have the case where both the bonds are simple. 
     elif #cfk gt 2 then
      if cfk[4] ne 5 then
       if cfy[3]+cfx[3] ge 2*cfk[3]+2 then
        act[k][i]:=0;
       elif cfy[3]+cfx[3] eq 2*cfk[3] then
        act[k][i]:=i;
       else
        cfk:=[k,0,cfy[3]+cfx[3]-cfk[3],cfk[4]];
        Include(~nextrt,cfk);
        ind:=Index(eroots,nextrt);
        if ind eq 0 then
         Include(~eroots,nextrt);
         act[k][i]:=#eroots;
         act[k][#eroots]:=i;
        else
         act[k][i]:=ind;
         act[k][ind]:=i;
        end if;
       end if;
      else
       cc:=cfx[2]+cfy[2]-cfk[2];
       ccc:=-cfk[3];
       if #cfx gt 2 then
        ccc:=ccc+cfx[3];
       end if;
       if #cfy gt 2 then
        ccc:=ccc+cfy[3];
       end if;
       if cc + ccc ge 2 + cfk[2] + cfk[3] then
        act[k][i]:=0;
       elif (cc eq cfk[2]) and (ccc eq cfk[3]) then
        act[k][i]:=i;
       else
        if ccc eq 0 then
         cfk:=<k,cc>;
        else
	 root := RootOfUnity(2*5, C);
         cfk:=<k,cc+ccc*(root + root^-1)>;
        end if;
        Include(~nextrt,cfk);
        ind:=Index(eroots,nextrt);
        if ind eq 0 then
         Include(~eroots,nextrt);
         act[k][i]:=#eroots;
         act[k][#eroots]:=i;
        else
         act[k][i]:=ind;
         act[k][ind]:=i;
        end if;
       end if;
      end if;
     elif #cfx gt 2 then
      if #cfy gt 2 then
       act[k][i]:=0;
      elif cfy[2]+cfx[2]+cfx[3] ge 2*cfk[2]+2 then
       act[k][i]:=0;
      else
       cfk:=[k,cfx[2]+cfy[2]-cfk[2],cfx[3],cfx[4]];
       Include(~nextrt,cfk);
       ind:=Index(eroots,nextrt);
       if ind eq 0 then
        Include(~eroots,nextrt);
        act[k][i]:=#eroots;
        act[k][#eroots]:=i;
       else
        act[k][i]:=ind;
        act[k][ind]:=i;
       end if;
      end if;
     elif #cfy gt 2 then
      if cfy[2]+cfy[3]+cfx[2] ge 2*cfk[2]+2 then
       act[k][i]:=0;
      else
       cfk:=[k,cfx[2]+cfy[2]-cfk[2],cfy[3],cfy[4]];
       Include(~nextrt,cfk);
       ind:=Index(eroots,nextrt);
       if ind eq 0 then
        Include(~eroots,nextrt);
        act[k][i]:=#eroots;
        act[k][#eroots]:=i;
       else
        act[k][i]:=ind;
        act[k][ind]:=i;
       end if;
      end if;
     elif cfx[2]+cfy[2] ge 2*cfk[2]+2 then
      act[k][i]:=0;
     else
      cfk:=[k,cfx[2]+cfy[2]-cfk[2]];
      Include(~nextrt,cfk);
      ind:=Index(eroots,nextrt);
      if ind eq 0 then
       Include(~eroots,nextrt);
       act[k][i]:=#eroots;
       act[k][#eroots]:=i;
      else
       act[k][i]:=ind;
       act[k][ind]:=i;
      end if;
     end if;
// Here we consider the case where there is only one bond to the k-th simple 
// root.
    else
     x:=neighbours[1][1];
     cfx:=neighbours[1];
     cfk:=eroots[i][indk];
// Firstly, the case where this bond is simple.
     if mx[k][x] eq 3 then
      if #cfk gt 2 then
       if cfx[2] ne 0 then
        if (cfx[2] eq 2*cfk[2]) and (cfx[3] eq 2*cfk[3]) then
         act[k][i]:=i;
        else
         if cfk[3] ne cfx[3] then
          cfk[3]:=cfx[3]-cfk[3];
          cfk[2]:=cfx[2]-cfk[2];
          Include(~nextrt,cfk);
         elif cfk[2] ne cfx[2] then
          cfk[2]:=cfx[2]-cfk[2];
          Prune(~cfk);
          Prune(~cfk);
          Include(~nextrt,cfk);
         end if;
         ind:=Index(eroots,nextrt);
         if ind eq 0 then
          Include(~eroots,nextrt);
          act[k][i]:=#eroots;
          act[k][#eroots]:=i;
         else
          act[k][i]:=ind;
          act[k][ind]:=i;
         end if;
        end if;
       elif cfx[3] ge 4*cfk[3] then
        act[k][i]:=0;
       elif cfx[3] eq 2*cfk[3] then
        act[k][i]:=i;
       else
        if cfx[3] ne 1 then
         cfk[3]:=cfx[3]-cfk[3];
         Include(~nextrt,cfk);
        end if;
        ind:=Index(eroots,nextrt);
        if ind eq 0 then
         Include(~eroots,nextrt);
         act[k][i]:=#eroots;
         act[k][#eroots]:=i;
        else
         act[k][i]:=ind;
         act[k][ind]:=i;
        end if;
       end if;
      elif #cfx gt 2 then
       cfk[3]:=1;
       cfk[4]:=cfx[4];
       if cfx[2] eq 2 then
        cfk[2]:=1;
       else
        cfk[2]:=0;
       end if;
       Include(~nextrt,cfk);
       ind:=Index(eroots,nextrt);
       if ind eq 0 then
        Include(~eroots,nextrt);
        act[k][i]:=#eroots;
        act[k][#eroots]:=i;
       else
        act[k][i]:=ind;
        act[k][ind]:=i;
       end if;
      else
       if cfx[2] ge 2*cfk[2] + 2 then
        act[k][i]:=0;
       elif cfx[2] eq 2*cfk[2] then
        act[k][i]:=i;
       else
        if cfx[2] ne 1 then
         cfk[2]:=cfx[2]-cfk[2];
         Include(~nextrt,cfk);
        end if;
        ind:=Index(eroots,nextrt);
        if ind eq 0 then
         Include(~eroots,nextrt);
         act[k][i]:=#eroots;
         act[k][#eroots]:=i;
        else
         act[k][i]:=ind;
         act[k][ind]:=i;
        end if;
       end if;
      end if;
// Secondly, the case where the bond is not simple.     
     elif #cfk gt 2 then  
      if #cfx eq 2 then
       if cfx[2] eq 2 then
        act[k][i]:=i;
       else
        ind:=Index(eroots,nextrt);
        if ind eq 0 then
         Include(~eroots,nextrt);
         act[k][i]:=#eroots;
         act[k][#eroots]:=i;
        else
         act[k][i]:=ind;
         act[k][ind]:=i;
        end if;
       end if;
      elif (cfk[2] eq 2) and (cfk[3] eq 0) then
       if cfx[3] eq 2 then
        act[k][i]:=0;
       else
        cfk:=<k,1>;
        Include(~nextrt,cfk);
        ind:=Index(eroots,nextrt);
        if ind eq 0 then
         Include(~eroots,nextrt);
         act[k][i]:=#eroots;
         act[k][#eroots]:=i;
        else
         act[k][i]:=ind;
         act[k][ind]:=i;
        end if;
       end if;
      else
       cfk[2]:=cfx[3]-cfk[2];
       if cfx[2] + cfx[3] eq cfk[3] then
        Prune(~cfk);
        Prune(~cfk);
       else
        cfk[3]:= cfx[2] + cfx[3] - cfk[3];
       end if;
       Include(~nextrt,cfk);
       ind:=Index(eroots,nextrt);
       if ind eq 0 then
        Include(~eroots,nextrt);
        act[k][i]:=#eroots;
        act[k][#eroots]:=i;
       else
        act[k][i]:=ind;
        act[k][ind]:=i;
       end if;
      end if;
// Now the case where the coefficient of k is an integer.
// Why is cfx[3] defined? Or do the if statements apply even if the entry is undefinend?
     else
      if cfx[3] ne 1 then
       act[k][i]:=0;
      elif cfx[4] eq 4 then
       act[k][i]:=i;
      else
       if cfx[4] eq 5 then
        cfk:=<k,0+1*(root5 + root5i)>;
       else
	root := RootOfUnity(2*mx[k, x], C);
	rooti := root^-1;
        cfk:=<k,(root^(2+1) - rooti^(2+1))/(root - rooti)>;
       end if;
       Include(~nextrt,cfk);
       ind:=Index(eroots,nextrt);
       if ind eq 0 then
        Include(~eroots,nextrt);
        act[k][i]:=#eroots;
        act[k][#eroots]:=i;
       else
        act[k][i]:=ind;
        act[k][ind]:=i;
       end if;
      end if;
     end if;
    end if;
   end if;
  end if;
  if #eroots ge counter+500 then
   counter:=#eroots;
   i, counter;
  end if;
 end for;
 i +:= 1;
end while;

return act, eroots;

end function;
