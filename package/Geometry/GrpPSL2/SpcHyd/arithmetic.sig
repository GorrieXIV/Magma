174,1
S,Center,Returns the element in the upper half-plane which maps to 0 in D,0,1,0,0,0,0,0,0,0,SpcHyd,,-45,-38,-38,-38,-38,-38
S,Rotation,Returns the rotation used in the disc,0,1,0,0,0,0,0,0,0,SpcHyd,,-45,-38,-38,-38,-38,-38
S,DiscToPlane,Maps z in a unit disc to H,0,2,0,0,0,0,0,0,0,SpcHydElt,,0,0,SpcHyp,,SpcHypElt,-38,-38,-38,-38,-38
S,PlaneToDisc,Maps z in an upper half-plane to D,0,2,0,0,0,0,0,0,0,SpcHypElt,,0,0,SpcHyd,,SpcHydElt,-38,-38,-38,-38,-38
S,Matrix,Returns the matrix representation of g acting on the unit disc D,0,2,0,0,0,0,0,0,0,SpcHyd,,0,0,GrpPSL2Elt,,177,-38,-38,-38,-38,-38
S,IsExact,Returns true (and the exact value of the argument) iff x is exact,0,1,0,0,0,0,0,0,0,SpcHydElt,,36,-1,-38,-38,-38,-38
S,ExactValue,"Returns the exact value of the argument; if it does not exist, returns an error",0,1,0,0,0,0,0,0,0,SpcHydElt,,-1,-38,-38,-38,-38,-38
S,in,,0,2,0,0,0,0,0,0,0,SpcHyd,,0,0,-1,,36,-38,-38,-38,-38,-38
S,eq,,0,2,0,0,0,0,0,0,0,SpcHydElt,,0,0,SpcHydElt,,36,-38,-38,-38,-38,-38
S,*,,0,2,0,0,0,0,0,0,0,SpcHydElt,,0,0,-45,,-45,-38,-38,-38,-38,-38
S,*,,0,2,0,0,0,0,0,0,0,-45,,0,0,SpcHydElt,,-45,-38,-38,-38,-38,-38
S,+,,0,2,0,0,0,0,0,0,0,-45,,0,0,SpcHydElt,,-45,-38,-38,-38,-38,-38
S,+,,0,2,0,0,0,0,0,0,0,SpcHydElt,,0,0,-45,,-45,-38,-38,-38,-38,-38
S,+,,0,2,0,0,0,0,0,0,0,SpcHydElt,,0,0,SpcHydElt,,-45,-38,-38,-38,-38,-38
S,-,,0,1,0,0,0,0,0,0,0,SpcHydElt,,SpcHydElt,-38,-38,-38,-38,-38
S,-,,0,2,0,0,0,0,0,0,0,-45,,0,0,SpcHydElt,,-45,-38,-38,-38,-38,-38
S,-,,0,2,0,0,0,0,0,0,0,SpcHydElt,,0,0,-45,,-45,-38,-38,-38,-38,-38
S,-,,0,2,0,0,0,0,0,0,0,SpcHydElt,,0,0,SpcHydElt,,-45,-38,-38,-38,-38,-38
S,/,,0,2,0,0,0,0,0,0,0,-45,,0,0,SpcHydElt,,-45,-38,-38,-38,-38,-38
S,*,"Returns T(x), using the identification of the unit disc with the upper half-plane",0,2,0,0,0,0,0,0,0,SpcHydElt,,0,0,GrpPSL2Elt,,SpcHydElt,-38,-38,-38,-38,-38
