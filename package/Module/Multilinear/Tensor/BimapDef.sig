174,1
S,Print,Print U,0,1,0,0,1,0,0,0,0,BmpU,,-38,-38,-38,-38,-38,-38
S,Print,Print V,0,1,0,0,1,0,0,0,0,BmpV,,-38,-38,-38,-38,-38,-38
S,Print,Print u,0,1,0,0,1,0,0,0,0,BmpUElt,,-38,-38,-38,-38,-38,-38
S,Print,Print v,0,1,0,0,1,0,0,0,0,BmpVElt,,-38,-38,-38,-38,-38,-38
S,IsCoercible,"Decides if x can be coerced into U, and if so, returns the result",0,2,0,0,0,0,0,0,0,-1,,0,0,BmpU,,36,BmpUElt,-38,-38,-38,-38
S,IsCoercible,"Decides if x can be coerced into V, and if so, returns the result",0,2,0,0,0,0,0,0,0,-1,,0,0,BmpV,,36,BmpVElt,-38,-38,-38,-38
S,Parent,Returns the parent bilinear map for U,0,1,0,0,0,0,0,0,0,BmpU,,TenSpcElt,-38,-38,-38,-38,-38
S,Parent,Returns the parent bilinear map for V,0,1,0,0,0,0,0,0,0,BmpV,,TenSpcElt,-38,-38,-38,-38,-38
S,Parent,Returns the parent U for u,0,1,0,0,0,0,0,0,0,BmpUElt,,BmpU,-38,-38,-38,-38,-38
S,Parent,Returns the parent V for v,0,1,0,0,0,0,0,0,0,BmpVElt,,BmpV,-38,-38,-38,-38,-38
S,LeftDomain,Returns the left domain of B used for coercion,0,1,0,0,0,0,0,0,0,TenSpcElt,,BmpU,-38,-38,-38,-38,-38
S,RightDomain,Returns the right domain of B used for coercion,0,1,0,0,0,0,0,0,0,TenSpcElt,,BmpV,-38,-38,-38,-38,-38
S,eq,Decides if u1 and u2 are the same,0,2,0,0,0,0,0,0,0,BmpUElt,,0,0,BmpUElt,,36,-38,-38,-38,-38,-38
S,eq,Decides if v1 and v2 are the same,0,2,0,0,0,0,0,0,0,BmpVElt,,0,0,BmpVElt,,36,-38,-38,-38,-38,-38
S,eq,Decides if U1 and U2 are the same,0,2,0,0,0,0,0,0,0,BmpU,,0,0,BmpU,,36,-38,-38,-38,-38,-38
S,eq,Decides if V1 and V2 are the same,0,2,0,0,0,0,0,0,0,BmpV,,0,0,BmpV,,36,-38,-38,-38,-38,-38
S,*,u * v,0,2,0,0,0,0,0,0,0,BmpVElt,,0,0,BmpUElt,,-1,-38,-38,-38,-38,-38
S,*,X * Y,0,2,0,0,0,0,0,0,0,BmpV,,0,0,BmpU,,-1,-38,-38,-38,-38,-38
S,*,x * Y,0,2,0,0,0,0,0,0,0,BmpV,,0,0,BmpUElt,,-1,-38,-38,-38,-38,-38
S,*,X * Y,0,2,0,0,0,0,0,0,0,BmpVElt,,0,0,BmpU,,-1,-38,-38,-38,-38,-38
S,*,x * y,0,2,0,0,0,0,0,0,0,BmpUElt,,0,0,BmpVElt,,-1,-38,-38,-38,-38,-38
S,*,X * y,0,2,0,0,0,0,0,0,0,BmpUElt,,0,0,BmpV,,-1,-38,-38,-38,-38,-38
S,*,x * Y,0,2,0,0,0,0,0,0,0,BmpU,,0,0,BmpVElt,,-1,-38,-38,-38,-38,-38
S,*,X * Y,0,2,0,0,0,0,0,0,0,BmpU,,0,0,BmpV,,-1,-38,-38,-38,-38,-38
S,*,x * y,0,2,0,0,0,0,0,0,0,BmpUElt,,0,0,BmpUElt,,-1,-38,-38,-38,-38,-38
S,*,X * y,0,2,0,0,0,0,0,0,0,BmpUElt,,0,0,BmpU,,-1,-38,-38,-38,-38,-38
S,*,x * Y,0,2,0,0,0,0,0,0,0,BmpU,,0,0,BmpUElt,,-1,-38,-38,-38,-38,-38
S,*,X * Y,0,2,0,0,0,0,0,0,0,BmpU,,0,0,BmpU,,-1,-38,-38,-38,-38,-38
S,*,x * y,0,2,0,0,0,0,0,0,0,BmpVElt,,0,0,BmpVElt,,-1,-38,-38,-38,-38,-38
S,*,X * y,0,2,0,0,0,0,0,0,0,BmpVElt,,0,0,BmpV,,-1,-38,-38,-38,-38,-38
S,*,x * Y,0,2,0,0,0,0,0,0,0,BmpV,,0,0,BmpVElt,,-1,-38,-38,-38,-38,-38
S,*,X * Y,0,2,0,0,0,0,0,0,0,BmpV,,0,0,BmpV,,-1,-38,-38,-38,-38,-38
S,*,x * B,0,2,0,0,0,0,0,0,0,TenSpcElt,,0,0,-1,,TenSpcElt,-38,-38,-38,-38,-38
S,*,B * y,0,2,0,0,0,0,0,0,0,-1,,0,0,TenSpcElt,,-1,-38,-38,-38,-38,-38
