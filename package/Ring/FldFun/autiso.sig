174,1
A,FldFunG,1,ulp
V,ULP,2
S,FirstPoleElement,Return the first pole element and its pole order wrt D at P,0,2,0,0,0,0,0,0,0,230,,0,0,59,,-45,148,-38,-38,-38,-38
S,FirstPoleElement,Return the first pole element and its pole order at P,0,1,0,0,0,0,0,0,0,230,,-45,148,-38,-38,-38,-38
S,HasAlmostUniqueLocalUniformizer,"Compute an almost unique local uniformizer wrt D at P, if it exists",0,2,0,0,0,0,0,0,0,230,,0,0,59,,37,5,148,-38,-38,-38
S,HasAlmostUniqueLocalUniformizer,"Compute an almost unique local uniformizer at P, if it exists",0,1,0,0,0,0,0,0,0,230,,37,5,148,-38,-38,-38
S,HasAlmostUniqueLocalParametrization,"Returns the parametrization function wrt D at P, if it exists. The function takes the desired relative precision as second argument",0,2,0,0,0,0,0,0,0,230,,0,0,59,,37,41,-38,-38,-38,-38
S,HasAlmostUniqueLocalParametrization,"Returns the parametrization function at P, if it exists. The function takes the desired relative precision as second argument",0,1,0,0,0,0,0,0,0,230,,37,41,-38,-38,-38,-38
A,Map,11,static,do_magma_image,image,imageconstr,imagedone,do_magma_preimage,maybe_has_preimage,preimage,preimageconstr,preimagedone,components
S,Preimage,Return preimage of z under f,0,2,0,0,0,0,0,0,0,-1,,0,0,175,,-25,-38,-38,-38,-38,-38
S,HasPreimage,Return boolean and preimage of z under f if it exists,0,2,0,0,0,0,0,0,0,-1,,0,0,175,,37,-25,-38,-38,-38,-38
S,HasPreimageFunction,"True and the preimage function of f if it cen be determined, false otherwise",0,1,0,0,0,0,0,0,0,175,,37,41,-38,-38,-38,-38
S,Image,Return image of z under f,0,2,0,0,0,0,0,0,0,-1,,0,0,175,,-25,-38,-38,-38,-38,-38
S,HasImage,Return boolean and image of z under f if it exists,0,2,0,0,0,0,0,0,0,-1,,0,0,175,,37,-25,-38,-38,-38,-38
S,ImageFunction,The image function of f,0,1,0,0,0,0,0,0,0,175,,41,-38,-38,-38,-38,-38
S,MakeHomWithPreimageHandler,,0,4,0,0,0,0,0,0,0,-1,,0,0,-1,,0,0,-1,,0,0,-1,,175,-38,-38,-38,-38,-38
S,MakeMapWithPreimageHandler,,0,4,0,0,0,0,0,0,0,-1,,0,0,-1,,0,0,-1,,0,0,-1,,175,-38,-38,-38,-38,-38
A,SetFormal,1,data
A,Map,1,data
A,RngInt,2,FieldCategory,FunctionFieldCategory
A,Fld,1,FunctionFieldCategory
S,IsCategory,,0,1,0,0,0,0,0,0,0,-1,,37,-38,-38,-38,-38,-38
S,IsFieldCategory,,0,1,0,0,0,0,0,0,0,-1,,95,-38,-38,-38,-38,-38
S,IsMorphismCategory,,0,1,0,0,0,0,0,0,0,-1,,95,-38,-38,-38,-38,-38
S,IsMorphismCategory,Whether C is a morphism category of D,0,2,0,0,0,0,0,0,0,-1,,0,0,-1,,95,-38,-38,-38,-38,-38
S,IsExtensionCategory,,0,1,0,0,0,0,0,0,0,-1,,95,-38,-38,-38,-38,-38
S,IsExtensionCategory,,0,2,0,0,0,0,0,0,0,-1,,0,0,-1,,95,-38,-38,-38,-38,-38
S,IsFunctionFieldCategory,,0,1,0,0,0,0,0,0,0,-1,,95,-38,-38,-38,-38,-38
S,IsFunctionFieldCategory,,0,2,0,0,0,0,0,0,0,-1,,0,0,-1,,95,-38,-38,-38,-38,-38
S,HasFixedBaseObject,,0,1,0,0,0,0,0,0,0,-1,,-1,-38,-38,-38,-38,-38
S,BaseCategory,,0,1,0,0,0,0,0,0,0,95,,95,-1,-38,-38,-38,-38
S,SPrintCategory,,0,1,0,0,0,0,0,0,0,95,,298,-38,-38,-38,-38,-38
S,PrintCategory,,0,1,0,0,1,0,0,0,0,95,,-38,-38,-38,-38,-38,-38
S,ParentCategory,,0,1,0,0,0,0,0,0,0,175,,95,-38,-38,-38,-38,-38
S,IsObject,,0,1,0,0,0,0,0,0,0,95,,41,-38,-38,-38,-38,-38
S,IsMorphism,,0,1,0,0,0,0,0,0,0,95,,41,-38,-38,-38,-38,-38
S,AreEqualObjects,,0,1,0,0,0,0,0,0,0,95,,41,-38,-38,-38,-38,-38
S,AreEqualMorphisms,,0,1,0,0,0,0,0,0,0,95,,41,-38,-38,-38,-38,-38
S,HasMorphism,,0,1,0,0,0,0,0,0,0,95,,41,-38,-38,-38,-38,-38
S,Morphism,,0,1,0,0,0,0,0,0,0,95,,41,-38,-38,-38,-38,-38
S,HasMorphismFromImages,,0,1,0,0,0,0,0,0,0,95,,41,-38,-38,-38,-38,-38
S,MorphismFromImages,,0,1,0,0,0,0,0,0,0,95,,41,-38,-38,-38,-38,-38
S,HasMorphismFromImagesAndBaseMorphism,,0,1,0,0,0,0,0,0,0,95,,41,-38,-38,-38,-38,-38
S,MorphismFromImagesAndBaseMorphism,,0,1,0,0,0,0,0,0,0,95,,41,-38,-38,-38,-38,-38
S,SupportsExtension,,0,1,0,0,0,0,0,0,0,95,,41,-38,-38,-38,-38,-38
S,HasExtension,,0,1,0,0,0,0,0,0,0,95,,41,-38,-38,-38,-38,-38
S,Extension,,0,1,0,0,0,0,0,0,0,95,,41,-38,-38,-38,-38,-38
S,HasRightCancellation,,0,1,0,0,0,0,0,0,0,95,,41,-38,-38,-38,-38,-38
S,RightCancellation,,0,1,0,0,0,0,0,0,0,95,,41,-38,-38,-38,-38,-38
S,HasRestriction,,0,1,0,0,0,0,0,0,0,95,,41,-38,-38,-38,-38,-38
S,Restriction,,0,1,0,0,0,0,0,0,0,95,,41,-38,-38,-38,-38,-38
S,HasBaseExtension,,0,1,0,0,0,0,0,0,0,95,,41,-38,-38,-38,-38,-38
S,BaseExtension,,0,1,0,0,0,0,0,0,0,95,,41,-38,-38,-38,-38,-38
S,HasBaseExtensionMorphisms,,0,1,0,0,0,0,0,0,0,95,,41,-38,-38,-38,-38,-38
S,BaseExtensionMorphisms,,0,1,0,0,0,0,0,0,0,95,,41,-38,-38,-38,-38,-38
S,HasCoercion,,0,1,0,0,0,0,0,0,0,95,,41,-38,-38,-38,-38,-38
S,Coercion,,0,1,0,0,0,0,0,0,0,95,,41,-38,-38,-38,-38,-38
S,HasIdentity,,0,1,0,0,0,0,0,0,0,95,,41,-38,-38,-38,-38,-38
S,Identity,,0,1,0,0,0,0,0,0,0,95,,41,-38,-38,-38,-38,-38
S,IsIdentity,,0,1,0,0,0,0,0,0,0,95,,41,-38,-38,-38,-38,-38
S,ImportExternalMorphism,,0,1,0,0,0,0,0,0,0,95,,41,-38,-38,-38,-38,-38
S,HasComposition,,0,1,0,0,0,0,0,0,0,95,,41,-38,-38,-38,-38,-38
S,Composition,,0,1,0,0,0,0,0,0,0,95,,41,-38,-38,-38,-38,-38
S,HasCompositionSequence,,0,1,0,0,0,0,0,0,0,95,,41,-38,-38,-38,-38,-38
S,CompositionSequence,,0,1,0,0,0,0,0,0,0,95,,41,-38,-38,-38,-38,-38
S,Degree,,0,1,0,0,0,0,0,0,0,95,,41,-38,-38,-38,-38,-38
S,SpecifyInverseMorphisms,,0,1,0,0,0,0,0,0,0,95,,41,-38,-38,-38,-38,-38
S,HasInverse,,0,1,0,0,0,0,0,0,0,95,,41,-38,-38,-38,-38,-38
S,InstallInverseConstructor,,0,1,0,0,0,0,0,0,0,95,,41,-38,-38,-38,-38,-38
S,PreimageConstructorViaInverse,,0,1,0,0,0,0,0,0,0,95,,41,-38,-38,-38,-38,-38
S,IsIsomorphism,,0,1,0,0,0,0,0,0,0,95,,41,-38,-38,-38,-38,-38
S,IsEndomorphism,,0,1,0,0,0,0,0,0,0,95,,41,-38,-38,-38,-38,-38
S,IsAutomorphism,,0,1,0,0,0,0,0,0,0,95,,41,-38,-38,-38,-38,-38
S,IsIsomorphic,,0,1,0,0,0,0,0,0,0,95,,41,-38,-38,-38,-38,-38
S,HasIsomorphismExtension,,0,1,0,0,0,0,0,0,0,95,,41,-38,-38,-38,-38,-38
S,HasIsomorphismExtensions,,0,1,0,0,0,0,0,0,0,95,,41,-38,-38,-38,-38,-38
S,IsomorphismExtension,,0,1,0,0,0,0,0,0,0,95,,41,-38,-38,-38,-38,-38
S,IsomorphismExtensions,,0,1,0,0,0,0,0,0,0,95,,41,-38,-38,-38,-38,-38
S,HasMorphismAutomorphism,,0,1,0,0,0,0,0,0,0,95,,41,-38,-38,-38,-38,-38
S,HasMorphismAutomorphisms,,0,1,0,0,0,0,0,0,0,95,,41,-38,-38,-38,-38,-38
S,MorphismAutomorphism,,0,1,0,0,0,0,0,0,0,95,,41,-38,-38,-38,-38,-38
S,MorphismAutomorphisms,,0,1,0,0,0,0,0,0,0,95,,41,-38,-38,-38,-38,-38
S,HasIsomorphisms,,0,1,0,0,0,0,0,0,0,95,,41,-38,-38,-38,-38,-38
S,Isomorphisms,,0,1,0,0,0,0,0,0,0,95,,41,-38,-38,-38,-38,-38
S,HasAutomorphisms,,0,1,0,0,0,0,0,0,0,95,,41,-38,-38,-38,-38,-38
S,Automorphisms,,0,1,0,0,0,0,0,0,0,95,,41,-38,-38,-38,-38,-38
S,IsIsomorphicOverBase,,0,1,0,0,0,0,0,0,0,95,,41,-38,-38,-38,-38,-38
S,IsomorphismsOverBase,,0,1,0,0,0,0,0,0,0,95,,41,-38,-38,-38,-38,-38
S,BaseObject,,0,1,0,0,0,0,0,0,0,95,,41,-38,-38,-38,-38,-38
S,ExtensionMorphism,,0,1,0,0,0,0,0,0,0,95,,41,-38,-38,-38,-38,-38
S,HasFrobeniusEndomorphism,,0,1,0,0,0,0,0,0,0,95,,41,-38,-38,-38,-38,-38
S,FrobeniusEndomorphism,,0,1,0,0,0,0,0,0,0,95,,41,-38,-38,-38,-38,-38
S,IsFunctor,,0,1,0,0,0,0,0,0,0,175,,37,-38,-38,-38,-38,-38
S,Functor,,0,4,0,0,0,0,0,0,0,41,,0,0,41,,0,0,95,,0,0,95,,175,-38,-38,-38,-38,-38
S,Functor,,0,6,0,0,0,0,0,0,0,41,,0,0,41,,0,0,41,,0,0,41,,0,0,95,,0,0,95,,175,-38,-38,-38,-38,-38
S,ObjectMap,,0,1,0,0,0,0,0,0,0,175,,41,-38,-38,-38,-38,-38
S,MorphismMap,,0,1,0,0,0,0,0,0,0,175,,41,-38,-38,-38,-38,-38
S,ObjectMapHasPreimage,,0,1,0,0,0,0,0,0,0,175,,41,-38,-38,-38,-38,-38
S,MorphismMapHasPreimage,,0,1,0,0,0,0,0,0,0,175,,41,-38,-38,-38,-38,-38
S,IsPerfect,Return whether field is perfect,0,1,0,0,0,0,0,0,0,-24,,37,-38,-38,-38,-38,-38
S,IsPerfect,Return whether field is perfect,0,1,0,0,0,0,0,0,0,313,,37,-38,-38,-38,-38,-38
S,Degree,"The degree of F over its base, always infinity",0,1,0,0,0,0,0,0,0,239,,-1,-38,-38,-38,-38,-38
S,BaseField,The ground field of F,0,1,0,0,0,0,0,0,0,84,,84,-38,-38,-38,-38,-38
S,BaseField,The base field of F,0,1,0,0,0,0,0,0,0,239,,-24,-38,-38,-38,-38,-38
S,BaseField,The base field of F,0,1,0,0,0,0,0,0,0,313,,-24,-38,-38,-38,-38,-38
S,ISABaseField,Whether G is among the (recursively defined) base fields of F,0,2,0,0,0,0,0,0,0,-24,,0,0,-24,,37,-38,-38,-38,-38,-38
S,Degree,The degree of F over K,0,2,0,0,0,0,0,0,0,-24,,0,0,-24,,-1,-38,-38,-38,-38,-38
S,IsPrimeField,Whether F is a prime field,0,1,0,0,0,0,0,0,0,-24,,36,-38,-38,-38,-38,-38
S,ConstantField,The constant field of F,0,1,0,0,0,0,0,0,0,239,,-24,-38,-38,-38,-38,-38
S,IsSimple,,0,1,0,0,0,0,0,0,0,4,,36,-38,-38,-38,-38,-38
S,FieldCategory,Create category of fields,0,0,0,0,0,0,0,95,-38,-38,-38,-38,-38
S,CoefficientMorphism,The coefficient morphism of the field morphism f,0,1,0,0,0,0,0,0,0,175,,175,-38,-38,-38,-38,-38
S,Top,,0,1,0,0,0,0,0,0,0,175,,175,-38,-38,-38,-38,-38
S,Bottom,,0,1,0,0,0,0,0,0,0,175,,175,-38,-38,-38,-38,-38
S,MorphismCategory,Create morphism category of given category C,0,1,0,0,0,0,0,0,0,95,,95,-38,-38,-38,-38,-38
S,MorphismCategory,Create morphism category of given category C over base S,0,2,0,0,0,0,0,0,0,-1,,0,0,95,,95,-38,-38,-38,-38,-38
S,ExtensionCategory,Create extension category of given category C,0,1,0,0,0,0,0,0,0,95,,95,-38,-38,-38,-38,-38
S,ExtensionCategory,Create extension category of given category C ove base object S,0,2,0,0,0,0,0,0,0,-1,,0,0,95,,95,-38,-38,-38,-38,-38
S,FunctionFieldCategory,,0,0,0,0,0,0,0,95,-38,-38,-38,-38,-38
S,FunctionFieldCategory,,0,1,0,0,0,0,0,0,0,-24,,95,-38,-38,-38,-38,-38
S,Conorm,Return conorm of P under f,0,2,0,0,0,0,0,0,0,230,,0,0,175,,59,-38,-38,-38,-38,-38
S,Conorm,Return conorm of D under f,0,2,0,0,0,0,0,0,0,59,,0,0,175,,59,-38,-38,-38,-38,-38
S,Cotrace,Return cotrace of D under f,0,2,0,0,0,0,0,0,0,56,,0,0,175,,56,-38,-38,-38,-38,-38
S,Operation,Return result of operation of automorphism f on object x,0,2,0,0,0,0,0,0,0,-1,,0,0,175,,-1,-38,-38,-38,-38,-38
V,Aut1,3
V,Aut2,1
A,Map,1,M
A,FldFunG,3,coeffauts,autsfull,auts
S,IsMorphism,"True, if the map is a field or function field morphism, false otherwise",0,1,0,0,0,0,0,0,0,175,,37,-38,-38,-38,-38,-38
S,Equality,"True, if the two maps are both field morphisms or function field morphisms and are equal, false otherwise",0,2,0,0,0,0,0,0,0,175,,0,0,175,,37,-38,-38,-38,-38,-38
S,IdentityFieldMorphism,The identity automorphism of F,0,1,0,0,0,0,0,0,0,-24,,175,-38,-38,-38,-38,-38
S,IsIdentity,"True if f is the identity morphism, false otherwise",0,1,0,0,0,0,0,0,0,175,,175,-38,-38,-38,-38,-38
S,HasInverse,"Either ""true"" and the inverse map, or ""false"" if inverse does not exist, or ""unknown"" if it cannot be computed",0,1,0,0,0,0,0,0,0,175,,298,175,-38,-38,-38,-38
S,Composition,The composition of the morphisms f and g,0,2,0,0,0,0,0,0,0,175,,0,0,175,,175,-38,-38,-38,-38,-38
S,Isomorphisms,"Returns a sequence of isomorphisms, extending BaseMorphism if given",0,2,0,0,0,0,0,0,0,-3,,0,0,-3,,82,-38,-38,-38,-38,-38
S,Isomorphisms,"Returns a sequence of isomorphisms, extending the identity morphism of the base field, which map the place P1 to the place P2",0,4,0,0,0,0,0,0,0,230,,0,0,230,,0,0,-3,,0,0,-3,,82,-38,-38,-38,-38,-38
S,IsIsomorphic,"Returns whether isomorphic (wrt BaseMorphism), and an isomorphism",0,2,0,0,0,0,0,0,0,-3,,0,0,-3,,37,175,-38,-38,-38,-38
S,Automorphisms,"Returns a sequence of automorphisms, extending BaseMorphism if given",0,1,0,0,0,0,0,0,0,-3,,82,-38,-38,-38,-38,-38
S,Automorphisms,"Returns a sequence of automorphisms, extending the identity morphisms on the base field, which map the place P1 to the place P2",0,3,0,0,0,0,0,0,0,230,,0,0,230,,0,0,-3,,82,-38,-38,-38,-38,-38
S,AutomorphismGroup,"The automorphism group of the algebraic function field F, generated by automorphisms which extend BaseMorphism if given",0,1,0,0,0,0,0,0,0,-3,,121,175,-38,-38,-38,-38
S,Numeration,Returns a numeration of the finite set S,0,1,0,0,0,0,0,0,0,83,,175,-38,-38,-38,-38,-38
S,AutomorphismGroup,Returns a representation of the automorphism group of F fixing the constant field through f,0,2,0,0,0,0,0,0,0,175,,0,0,4,,-27,175,82,-38,-38,-38
