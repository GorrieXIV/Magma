freeze;

import "../AlgQEA/module.m" : TPOfQUAModules,
                              WtsAndVecsOfQEAModule,
                              HighWtsAndVecsOfQEAModule;
import "../AlgLie/module.m" : TPOfLieAlgebraModules, 
                              SymPowOfLieAlgebraModules,
                              ExtPowOfLieAlgebraModules,
                              WtsAndVecsOfLieAlgebraModule,
                              HighWtsAndVecsOfLieAlgebraModule;

declare attributes ModAlg: WeightsAndVectors, HighestWeightsAndVectors;

intrinsic ModuleWithBasis( Q::SeqEnum[ModAlgElt] ) -> ModAlg
{Given a sequence Q of vectors from an algebra module M, create the submodule 
of M whose basis is given by the vectors of Q.}

    
     require #Q gt 0 : "Invalid empty sequence";
     M:= Parent( Q[1] );
     A:= Algebra( M );
     F:= CoefficientRing( A );
     W:= RModule( F, Dimension(M) );
     V:= RModuleWithBasis( [ W!Eltseq(v) : v in Q ] ); 
     if IsLeftModule( M ) then
        
        act:= function( x, v )

              return W!Eltseq( x^M!Coordinates( W, v ) );

        end function;

        return Module( A, 
         map< CartesianProduct( A, V ) -> V | t :-> act( t[1], t[2] ) > );

     elif IsRightModule( M ) then

        act:= function( v, x )

              return W!Eltseq( (M!Coordinates( W, v ))^x );

        end function;

        return Module( A, 
         map< CartesianProduct( V, A ) -> V | t :-> act( t[1], t[2] ) > );


     end if;

end intrinsic;


intrinsic ActionMatrix( M::ModAlg, x::AlgElt ) ->  AlgMatElt
{The matrix of the action of x on the module M}


     if IsLeftModule( M ) then
        mm:= [ ];
        for v in Basis( M ) do
            Append( ~mm, Coordinates( M, x^v ) );
        end for;
        return Transpose( Matrix( mm ) );

     elif IsRightModule( M ) then
        mm:= [ ];
        for v in Basis( M ) do
            Append( ~mm, Coordinates( M, v^x ) );
        end for;
        return Matrix( mm );
     end if;


end intrinsic;


intrinsic TensorProduct( modules::[ModAlg] ) -> ModAlg, Map
{The tensor product of the algebra modules in the list}


      A:= Algebra( modules[1] );
      for i in [2..#modules] do
          require Type( Algebra(modules[i] ) ) eq Type( A ) : "The modules are not defined over the same algebra";
          require Algebra( modules[i] ) eq A :"The modules are not defined over the same algebra";
      end for;

      require (Type(A) eq AlgQUE) or (Type(A) eq AlgLie) : "Currently tensor products are only defined for modules over Lie algebras or quantized enveloping algebras";

      if Type(A) eq AlgQUE then
         M, f:= TPOfQUAModules( modules ); 
      else
         M, f:= TPOfLieAlgebraModules( modules );
      end if; 
      return M,f;

end intrinsic;

intrinsic SymmetricPower( V::ModAlg, n::RngIntElt ) -> ModAlg, Map
{The n-th symmetric power of V}


      A:= Algebra( V );

      require Type(A) eq AlgLie : "Currently symmetric powers are only defined for modules over Lie algebras";

      M, f:= SymPowOfLieAlgebraModules( V, n );

      return M,f;

end intrinsic;

intrinsic ExteriorPower( V::ModAlg, n::RngIntElt ) -> ModAlg, Map
{The n-th exterior power of V}


      A:= Algebra( V );

      require Type(A) eq AlgLie : "Currently exterior powers are only defined for modules over Lie algebras";

      require n le Dimension(V) : "The integer n cannot exceed the dimension of V";

      M, f:= ExtPowOfLieAlgebraModules( V, n );

      return M,f;

end intrinsic;


intrinsic DirectSum( modules::[ModAlg] ) -> ModAlg, SeqEnum, SeqEnum
{The direct sum of the modules in the sequence `modules'; and the
list of embedding maps and the list of projection maps.}

       require #modules ge 2 : "The sequence of modules has to have at least two elements.";

       A:= Algebra( modules[1] );
       if IsLeftModule( modules[1] ) then
          left:= true;
       else
          left:= false;
       end if;

       for i in [2..#modules] do
           require Type( Algebra(modules[i] ) ) eq Type( A ) : "The modules are not defined over the same algebra";
           require Algebra( modules[i] ) eq A :"The modules are not defined over the same algebra";
           require IsLeftModule( modules[i] ) eq left : "The modules are not all left (respectively right) modules.";
       end for;


       len:= #modules;
       dims:= [ Dimension(modules[i]) : i in [1..len] ];
       ddd:= [ 0 ];
       ddd cat:= [ &+[ dims[k] : k in [1..m] ] : m in [1..len] ];

       M:= RModule( CoefficientRing(A), ddd[len+1] );

       if left then
          act:= function( x, v )

             ev:= Eltseq( v );
             vec:= [ ];
             for i in [1..len] do
                 vec cat:= Eltseq( x^( 
                     modules[i]![ ev[k] : k in [ddd[i]+1..ddd[i+1]]] ) );
             end for;

             return M!vec;

          end function;

          W:= Module( A, 
            map< CartesianProduct( A, M ) -> M | t :-> act( t[1], t[2] ) > );
       else
         act:= function( v, x )

             ev:= Eltseq( v );
             vec:= [ ];
             for i in [1..len] do
                 vec cat:= Eltseq( ( 
                     modules[i]![ ev[k] : k in [ddd[i]+1..ddd[i+1]]] )^x );
             end for;

             return M!vec;

          end function;

          W:= Module( A, 
            map< CartesianProduct( M, A ) -> M | t :-> act( t[1], t[2] ) > );

       end if;

       emb_maps:= [PowerStructure(Map) | ];
       for i in [1..len] do

           f:= function( w ) 
               v:= Eltseq( Zero(W) );
               ew:= Eltseq( w );
               for j in [ddd[i]+1..ddd[i+1]] do
                   v[j]:= ew[j-ddd[i]];
               end for;
               return W!v;
           end function;

           Append( ~emb_maps, map< modules[i] -> W | w :-> f(w) > );
       end for;

       proj_maps:= [PowerStructure(Map) | ];
       for i in [1..len] do
           
           p:= function( v )
               ev:= Eltseq( v );
               w:= [ v[k] : k in [ddd[i]+1..ddd[i+1]] ];
               return modules[i]!w;
           end function;

           Append( ~proj_maps, map< W -> modules[i] | v :-> p(v) > );
       end for;

       return W, emb_maps, proj_maps;

end intrinsic;


intrinsic SubalgebraModule( B::Alg, M::ModAlg ) -> ModAlg
{M as a B-module, where B is a subalgebra of the acting algebra of M}


      A:= Algebra( M );
      require Zero(B) in A : "B is not a subalgebra of the algebra of the module";

      V:= RModule( CoefficientRing(M), Dimension(M) );
      if IsLeftModule( M ) then

         return Module( B, 
                 map< CartesianProduct( B, V ) -> V | 
                     t :->  V!Eltseq( (A!t[1])^M!Coordinates( V, t[2] ) ) > );
      else

         return Module( B, 
                 map< CartesianProduct( V, B ) -> V | 
                     t :->  V!Eltseq( M!Coordinates( V, t[1] )^(A!t[2]) ) > );

      end if;

end intrinsic;


intrinsic WeightsAndVectors( V::ModAlg ) -> SeqEnum, SeqEnum
{Weights and corresponding vectors of a module over a split semisimple Lie algebra or quantum group}

      if assigned V`WeightsAndVectors then
         list:= V`WeightsAndVectors;
         return list[1], list[2];
      end if;

      A:= Algebra( V );

      require (Type(A) eq AlgQUE) or (Type(A) eq AlgLie) : "Currently this function is only defined for modules over semisimple Lie algebras or quantized enveloping algebras";

      if Type(A) eq AlgQUE then
         wt,vv:= WtsAndVecsOfQEAModule( V ); 
      else
         require IsSemisimple( A ) : "This function is only defined for semisimple Lie algebras";
         wt,vv:= WtsAndVecsOfLieAlgebraModule( V ); 
      end if; 

      V`WeightsAndVectors:= [* wt, vv *];

      return wt, vv;


end intrinsic;

intrinsic HighestWeightsAndVectors( V::ModAlg ) -> SeqEnum, SeqEnum
{Highest weights and corresponding vectors of a module over a split semisimple Lie algebra or quantum group}

      if assigned V`HighestWeightsAndVectors then
         list:= V`HighestWeightsAndVectors;
         return list[1], list[2];
      end if;

      A:= Algebra( V );

      require (Type(A) eq AlgQUE) or (Type(A) eq AlgLie) : "Currently this function is only defined for modules over semisimple Lie algebras or quantized enveloping algebras";

      if Type(A) eq AlgQUE then
         wt,vv:= HighWtsAndVecsOfQEAModule( V ); 
      else
         require IsSemisimple( A ) : "This function is only defined for semisimple Lie algebras";
         // The repn version seems to work better for pos char
	 rho := hom< A -> MatrixLieAlgebra(BaseRing(V),Dimension(V)) |
	   x :->  ActionMatrix(V,x) >;
         wts,wvs := HighestWeights(rho:Basis:="Weight");
	 wt := [];  vv := [V|];
	 for i in [1..#wts] do
	   for v in Basis(wvs[i]) do
	     Append( ~wt, wts[i] );  Append( ~vv, v );
	   end for;
	 end for;
	 
         //wt,vv:= HighWtsAndVecsOfLieAlgebraModule( V ); 
      end if; 

      V`HighestWeightsAndVectors:= [* wt, vv *];

      return wt, vv;


end intrinsic;
