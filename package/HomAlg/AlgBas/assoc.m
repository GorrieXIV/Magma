freeze;

/*
declare attributes SetEnum: assoc_keys, assoc_values;                          
                                                                               
intrinsic AssociativeArray() -> SetEnum                          
{Returns an empty associative array with keys lying in K and values            
lying in V}                                                                    
    S := { 1 };                                            
    S`assoc_keys := {@ @};                                                 
    S`assoc_values := [ ];                                                 
    return S;                                                                  
end intrinsic;                                                                 
                                                                               
intrinsic AAGet(A::SetEnum, k::.) -> .                                         
{Returns the value of the associative array A indexed by key k}                
    require assigned A`assoc_keys: "Argument is not an associative array";     
    require assigned A`assoc_values: "Argument is not an associative           
array";                                                                        
    keys := A`assoc_keys;                                                      
    values := A`assoc_values;                                                  
    n := Index(keys, k);                                                       
    require n gt 0: "Key is not present in associative array";                 
    require IsDefined(values, n): "Key has no associated value assigned";      
    return values[n];                                                          
end intrinsic;                                                                 
                                                                               
intrinsic AASet(A::SetEnum, k::., v::.)                                        
{Sets the value of the associative array A indexed by key k to v}              
    require assigned A`assoc_keys: "Argument is not an associative array";     
    require assigned A`assoc_values: "Argument is not an associative           
array";                                                                        
    keys := A`assoc_keys;                                                      
    values := A`assoc_values;                                                  
    n := Index(keys, k);                                                       
    if n eq 0 then                                                             
        Include(~keys, k);                                                     
        n := #keys;                                                            
        A`assoc_keys := keys;                                                  
    end if;                                                                    
    values[n] := v;                                                            
    A`assoc_values := values;                                                  
end intrinsic;                                                                 

intrinsic IsDefined(A::SetEnum, k::.) -> BoolElt, .                              
{Returns whether the associative array A contains a value with key k.  If      
so, this value is also returned}                                               
    require assigned A`assoc_keys: "Argument is not an associative array";     
    require assigned A`assoc_values: "Argument is not an associative           
array";                                                                        
    keys := A`assoc_keys;                                                      
    values := A`assoc_values;                                                  
    n := Index(keys, k);                                                       
    if n eq 0 then return false, _; end if;                                    
    require IsDefined(values, n): "Key has no associated value assigned";      
    return true, values[n];                                                    
end intrinsic;                                                                 
*/
