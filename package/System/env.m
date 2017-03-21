freeze;

/*
Routines dealing with "environment" objects -- essentially a mechanism
for getting global state that is only locally accessible.  The intrinsic
NewEnv() takes the names to refer to the values by and returns two
functions, get() and set().  Example usage pattern:

    > get,set := NewEnv(["foo", "bar"]);
    > set("foo", 3);
    > set("bar", "Hello!");
    > get("bar");
    Hello!

There is currently no way to tell if the value is assigned or not, or
to unassign a value.  This may be addressed if there is enough need.
*/

intrinsic NewEnv(S::[MonStgElt]) -> UserProgram, UserProgram
{Returns a new environment object with field names from S}
    env := { Integers() | };	// Give it a universe to enforce creation

    // Ensure that the names in S are valid
    for name in S do
	AddAttribute(SetEnum, name);
    end for;

    get := func<name | env``name>;

    // We have to do this because we are not allowed to directly modify
    // a value which is not an argument
    setsub := procedure(env, name, val) env``name := val; end procedure;
    set := proc<name, val | setsub(env, name, val) >;

    return get, set;
end intrinsic;


/*
Expanding on the concept, we introduce the idea of a store (which in
practice is what people wanted the global state for).
*/
declare attributes SetEnum: DataStore;
store_fmt := recformat<get : UserProgram, set: UserProgram,
			isset: UserProgram, del: UserProgram,
			keys: UserProgram, empty: UserProgram>;

intrinsic NewStore() -> Rec
{Returns a new data storage object}
    env := { Integers() | };	// Need a universe to avoid the global null

    env`DataStore := AssociativeArray(Strings());

    getfunc := func<name | env`DataStore[name]>;

    // We need this subprocedure because we are not allowed to
    // directly modify a value which is not an argument
    setsub := procedure(env, name, val)
	env`DataStore[name] := val;
    end procedure;
    setfunc := proc<name, val | setsub(env, name, val) >;

    issetfunc := func<name | IsDefined(env`DataStore, name)>;

    delsub := procedure(env, name)
	Remove(~env`DataStore, name);
    end procedure;
    delfunc := proc<name | delsub(env, name)>;

    keyfunc := func<| Keys(env`DataStore)>;

    emptysub := procedure(env)
	env`DataStore := AssociativeArray(Strings());
    end procedure;
    emptyfunc := proc<| emptysub(env)>;

    return rec<store_fmt | get := getfunc, set := setfunc,
    			isset := issetfunc, del := delfunc,
			keys := keyfunc, empty := emptyfunc>;
end intrinsic;

intrinsic StoreSet(store::Rec, field::MonStgElt, value::Any)
{Associates value to field in the store}
    store`set(field, value);
end intrinsic;

intrinsic StoreGet(store::Rec, field::MonStgElt) -> Any
{Returns the value associated to field in the store}
    ok,value := store`isset(field);
    error if not ok, "No such value present in the store";
    return value;
end intrinsic;

intrinsic StoreIsDefined(store::Rec, field::MonStgElt) -> BoolElt, Any
{Returns whether the field has an associated value in the store,
and if so returns this value also}
    return store`isset(field);
end intrinsic;

intrinsic StoreRemove(store::Rec, field::MonStgElt)
{Removes the association for the field in the store, if any}
    store`del(field);
end intrinsic;

intrinsic StoreKeys(store::Rec) -> SetEnum[MonStgElt]
{Returns the set of fields with defined values in the store}
    return store`keys();
end intrinsic;

intrinsic StoreClear(store::Rec)
{Removes all entries from the store}
    store`empty();
end intrinsic;

