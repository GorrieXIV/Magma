/*
# Character: X3
# Comment: 
# Ind: 0
# Ring: Z(i)
# Sparsity: 65%
# Checker result: pass
# Conjugacy class representative result: pass

local a, A, b, B, c, C, w, W, i, result, delta, idmat;

result := rec();
*/

E := RootOfUnity;

w := E(3); W := E(3)^2;
a := E(5)+E(5)^4; A := -1-a; //# b5, b5*
b := E(7)+E(7)^2+E(7)^4; B := -1-b;  //# b7, b7**
c := E(11)+E(11)^3+E(11)^4+E(11)^5+E(11)^9; C := -1-c; //# b11, b11**
i := E(4);
//result.comment := "Sz8 as 14 x 14 matrices\n";

result := [
[[0,0,1,0,0,0,0,0,0,0,0,0,0,0],
[0,0,0,0,1,0,0,0,0,0,0,0,0,0],
[1,0,0,0,0,0,0,0,0,0,0,0,0,0],
[0,0,0,0,0,0,0,1,0,0,0,0,0,0],
[0,1,0,0,0,0,0,0,0,0,0,0,0,0],
[0,0,0,0,0,0,0,0,0,0,1,0,0,0],
[0,0,0,0,0,0,-1,0,0,0,0,0,0,0],
[0,0,0,1,0,0,0,0,0,0,0,0,0,0],
[-1-i,1,i,-3*i,-1-i,i,-1,-1-i,-i,-1,2,-2+i,-1,-1+i],
[0,0,0,0,0,0,0,0,0,-1,0,0,0,0],
[0,0,0,0,0,1,0,0,0,0,0,0,0,0],
[-2-i,2,1+i,-1-2*i,-2,2*i,-1+i,0,0,i,1-i,-1+i,-1,i],
[2,-2+i,-3,2-2*i,3-2*i,-i,-2*i,-1-2*i,-2*i,-2-i,2+3*i,-2+i,0,-1],
[2*i,-1-2*i,1-i,-3+i,i,2-i,1+i,0,-2,1+i,-1-2*i,3+i,1+i,1]]
,
[[0,0,0,1,0,0,0,0,0,0,0,0,0,0],
[0,0,0,0,0,1,0,0,0,0,0,0,0,0],
[0,0,0,0,0,0,1,0,0,0,0,0,0,0],
[0,0,0,0,0,0,0,0,1,0,0,0,0,0],
[0,0,0,0,0,0,0,0,0,1,0,0,0,0],
[0,0,0,0,0,0,0,0,0,0,0,1,0,0],
[0,0,0,0,0,0,0,0,0,0,0,0,1,0],
[0,0,0,0,0,0,0,0,0,0,0,0,0,1],
[-1,0,0,-1,0,0,0,0,-1,0,0,0,0,0],
[-1,1,1+i,-2-i,-2,i,-1+i,-1+i,-1,i,1-2*i,1+2*i,i,1+i],
[-i,i,-1+i,1-i,-i,-1,-i,0,0,-1,1+i,-1,0,0],
[1+i,-2-i,-1-3*i,2+4*i,2+2*i,-i,2,2,1+i,2-2*i,-4+2*i,1-4*i,1-i,-2*i
  ],
[-2*i,1+2*i,3*i,-2-4*i,-1-3*i,0,-1,-2,-1-i,-3+i,3-i,-2+3*i,-1,2*i],
[-i,1+2*i,-1+2*i,1-2*i,-2*i,-1,-1-i,-1,1-i,-2,3+i,-2+2*i,-1,0]]];

return result;

