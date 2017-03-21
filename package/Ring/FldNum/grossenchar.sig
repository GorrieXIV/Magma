174,1
T,GrossenChar,-,0
A,GrossenChar,8,hecke,evalf,type,wt,dirich,zetas,clreps,roots
A,GrossenChar,1,field_is_cm
S,PrintNamed,Print Grossencharacter,0,3,0,0,1,0,0,0,0,298,,0,0,298,,0,0,GrossenChar,,-38,-38,-38,-38,-38,-38
S,IsCoercible,coerce,0,2,0,0,0,0,0,0,0,-1,,0,0,GrossenChar,,36,-1,-38,-38,-38,-38
S,in,in,0,2,0,0,0,0,0,0,0,GrossenChar,,0,0,-1,,36,-38,-38,-38,-38,-38
S,Conductor,"Given a Hecke Grossencharacter, return its conductor as an ideal and a sequence of real places",0,1,0,0,0,0,0,0,0,GrossenChar,,217,82,-38,-38,-38,-38
S,Modulus,"Given a Hecke Grossencharacter, return its modulus as an ideal and a sequence of real places",0,1,0,0,0,0,0,0,0,GrossenChar,,217,82,-38,-38,-38,-38
S,IsPrimitive,Whether or not a Grossencharacter is primitive,0,1,0,0,0,0,0,0,0,GrossenChar,,36,-38,-38,-38,-38,-38
A,FldNum,4,extension_field,Hip,grossen_array,ext_roots
S,@,eval,0,2,0,0,0,0,0,0,0,GrossenChar,,0,0,148,,-45,-38,-38,-38,-38,-38
S,@,eval,0,2,0,0,0,0,0,0,0,GrossenChar,,0,0,267,,-45,-38,-38,-38,-38,-38
S,@,eval,0,2,0,0,0,0,0,0,0,GrossenChar,,0,0,216,,-45,-38,-38,-38,-38,-38
S,@,eval,0,2,0,0,0,0,0,0,0,GrossenChar,,0,0,28,,-45,-38,-38,-38,-38,-38
S,@,eval,0,2,0,0,0,0,0,0,0,GrossenChar,,0,0,324,,172,-38,-38,-38,-38,-38
S,RawEval,RawEval,0,2,0,0,0,0,0,0,0,GrossenChar,,0,0,324,,28,52,52,-38,-38,-38
S,Grossencharacter,"Given a Hecke character along with a compatible infinity-type, try to find a suitable Dirichlet character on the units, and then return the induced Hecke Grossencharacter",1,1,1,82,1,82,0,148,2,0,0,0,0,0,0,0,82,,0,0,GrpHeckeElt,,GrossenChar,-38,-38,-38,-38,-38
S,Grossencharacter,"Given a Hecke character along with a compatible infinity-type and Dirichlet character, return the induced Hecke Grossencharacter",1,2,1,82,1,82,0,148,3,0,0,0,0,0,0,0,82,,0,0,GrpDrchNFElt,,0,0,GrpHeckeElt,,GrossenChar,-38,-38,-38,-38,-38
S,GrossenCheck,"Given an ideal in a CM field and an oo-type, determine whether the oo-type trivialises all units that are 1 mod I",1,1,1,82,1,82,0,148,2,0,0,0,0,0,0,0,82,,0,0,217,,36,28,-38,-38,-38,-38
S,*,Multiply,0,2,0,0,0,0,0,0,0,GrpHeckeElt,,0,0,GrossenChar,,GrossenChar,-38,-38,-38,-38,-38
S,*,Multiply,0,2,0,0,0,0,0,0,0,GrossenChar,,0,0,GrpHeckeElt,,GrossenChar,-38,-38,-38,-38,-38
S,*,Multiply,0,2,0,0,0,0,0,0,0,GrpDrchNFElt,,0,0,GrossenChar,,GrossenChar,-38,-38,-38,-38,-38
S,*,Multiply,0,2,0,0,0,0,0,0,0,GrossenChar,,0,0,GrpDrchNFElt,,GrossenChar,-38,-38,-38,-38,-38
S,/,Divide,0,2,0,0,0,0,0,0,0,GrossenChar,,0,0,GrpHeckeElt,,GrossenChar,-38,-38,-38,-38,-38
S,/,Divide,0,2,0,0,0,0,0,0,0,GrpHeckeElt,,0,0,GrossenChar,,GrossenChar,-38,-38,-38,-38,-38
S,/,Divide,0,2,0,0,0,0,0,0,0,GrossenChar,,0,0,GrpDrchNFElt,,GrossenChar,-38,-38,-38,-38,-38
S,/,Divide,0,2,0,0,0,0,0,0,0,GrpDrchNFElt,,0,0,GrossenChar,,GrossenChar,-38,-38,-38,-38,-38
S,^,Power,0,2,0,0,0,0,0,0,0,148,,0,0,GrossenChar,,GrossenChar,-38,-38,-38,-38,-38
S,*,Multiply,0,2,0,0,0,0,0,0,0,GrossenChar,,0,0,GrossenChar,,GrossenChar,-38,-38,-38,-38,-38
S,/,Divide,0,2,0,0,0,0,0,0,0,GrossenChar,,0,0,GrossenChar,,GrossenChar,-38,-38,-38,-38,-38
S,/,Divide,0,2,0,0,0,0,0,0,0,GrossenChar,,0,0,148,,GrossenChar,-38,-38,-38,-38,-38
A,GrossenChar,1,components
S,Components,"Given a Grossencharacter, return the components of its Dirichlet-Hecke restriction, as an associative array indexed by ramified places",0,1,0,0,0,0,0,0,0,GrossenChar,,457,-38,-38,-38,-38,-38
S,Component,"Given a Grossencharacter, return its Dirichlet component at P (a prime ideal)",0,2,0,0,0,0,0,0,0,217,,0,0,GrossenChar,,GrpDrchNFElt,-38,-38,-38,-38,-38
S,Component,"Given a Grossencharacter, return its Dirichlet component at an infinite place",0,2,0,0,0,0,0,0,0,148,,0,0,GrossenChar,,GrpDrchNFElt,-38,-38,-38,-38,-38
S,Component,"Given a Grossencharacter, return its Dirichlet component at a given place",0,2,0,0,0,0,0,0,0,332,,0,0,GrossenChar,,GrpDrchNFElt,-38,-38,-38,-38,-38
S,RootNumber,"Given a Grossencharacter and a prime ideal, return the local root number",0,2,0,0,0,0,0,0,0,217,,0,0,GrossenChar,,172,-38,-38,-38,-38,-38
S,RootNumber,"Given a Hecke character and a prime ideal, return the local root number",0,2,0,0,0,0,0,0,0,217,,0,0,GrpHeckeElt,,172,-38,-38,-38,-38,-38
S,RootNumber,"Given a Grossencharacter and a place, return the local root number",0,2,0,0,0,0,0,0,0,332,,0,0,GrossenChar,,172,-38,-38,-38,-38,-38
S,RootNumber,"Given a Hecke character and a place, return the local root number",0,2,0,0,0,0,0,0,0,332,,0,0,GrpHeckeElt,,172,-38,-38,-38,-38,-38
S,RootNumbers,"Given a Grossencharacter, return the root numbers at bad places",0,1,0,0,0,0,0,0,0,GrossenChar,,82,-38,-38,-38,-38,-38
S,RootNumbers,"Given a Hecke character, return the root numbers at bad places",0,1,0,0,0,0,0,0,0,GrpHeckeElt,,82,-38,-38,-38,-38,-38
S,RootNumber,"Given a Grossencharacter, compute its global root number",0,1,0,0,0,0,0,0,0,GrossenChar,,172,-38,-38,-38,-38,-38
S,RootNumber,"Given a Hecke character, compute its global root number",0,1,0,0,0,0,0,0,0,GrpHeckeElt,,172,-38,-38,-38,-38,-38
S,RootNumber,"Given a Grossencharacter and a rational prime p, compute its root number",0,2,0,0,0,0,0,0,0,148,,0,0,GrossenChar,,172,-38,-38,-38,-38,-38
S,RootNumber,"Given a Hecke character and a rational prime p, compute its root number",0,2,0,0,0,0,0,0,0,148,,0,0,GrpHeckeElt,,172,-38,-38,-38,-38,-38
S,Extend,Extend a Grossencharacter to the given ideal,0,2,0,0,0,0,0,0,0,217,,0,0,GrossenChar,,GrossenChar,-38,-38,-38,-38,-38
S,Extend,Extend a Grossencharacter to the given ideal and possible oo places,1,2,1,82,0,148,3,0,0,0,0,0,0,0,82,,0,0,217,,0,0,GrossenChar,,GrossenChar,-38,-38,-38,-38,-38
S,Restrict,Restrict a Grossencharacter to the given ideal,0,2,0,0,0,0,0,0,0,217,,0,0,GrossenChar,,GrossenChar,-38,-38,-38,-38,-38
S,Restrict,Restrict a Grossencharacter to the given ideal and possible oo places,1,2,1,82,0,148,3,0,0,0,0,0,0,0,82,,0,0,217,,0,0,GrossenChar,,GrossenChar,-38,-38,-38,-38,-38
S,AssociatedPrimitiveGrossencharacter,Return the associated primitive Grossencharacter of a given one,0,1,0,0,0,0,0,0,0,GrossenChar,,GrossenChar,-38,-38,-38,-38,-38
S,AssociatedPrimitiveCharacter,Return the associated primitive Grossencharacter of a given one,0,1,0,0,0,0,0,0,0,GrossenChar,,GrossenChar,-38,-38,-38,-38,-38
S,Weight,"Given a Hecke Grossencharacter, returns its weight",0,1,0,0,0,0,0,0,0,GrossenChar,,148,-38,-38,-38,-38,-38
S,CentralCharacter,"Given a Hecke Grossencharacter, compute its central Dirichlet character down to Q (normalised to have weight 0)",0,1,0,0,0,0,0,0,0,GrossenChar,,GrpDrchNFElt,-38,-38,-38,-38,-38
S,GrossenTwist,"Given a Grossencharacter, find its twist by a Hecke character (of the same modulus as the Grossencharacter) which numerically matches the given data (if possible)",0,2,0,0,0,0,0,0,0,168,,0,0,GrossenChar,,GrossenChar,GrpHecke,-38,-38,-38,-38
S,TateTwist,"Given a Grossencharacter, return its Tate twist by z",0,2,0,0,0,0,0,0,0,148,,0,0,GrossenChar,,GrossenChar,-38,-38,-38,-38,-38
S,TateTwist,"Given a Hecke character, return its Tate twist by z as a Grossencharacter",0,2,0,0,0,0,0,0,0,148,,0,0,GrpHeckeElt,,GrossenChar,-38,-38,-38,-38,-38
S,Grossencharacter,"Given an elliptic curve over Q with CM by an imaginary quadratic order, return the associated Grossencharacter",1,0,1,334,0,262,1,0,0,0,0,0,0,0,334,,GrossenChar,-38,-38,-38,-38,-38
S,EllipticCurve,"Given a suitable Grossencharacter over a class number one imaginary quadratic field, return the associated elliptic curve over Q",0,1,0,0,0,0,0,0,0,GrossenChar,,334,-38,-38,-38,-38,-38
