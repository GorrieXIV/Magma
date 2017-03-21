LoadPackage("AtlasRep");

# All sporadics and Tits group
names := ["Co1", "Co2", "Co3", "J1", "J2", "J3", "J4", 
          "M11", "M12", "M22", "M23", "M24", 
          "Fi22", "Fi23", "Fi24'", "B", "M", "HS", "McL", "Suz", "He",
          "Th", "Ly", "Ru", "O'N", "2F4(2)'"];

sporadics := [];
j := 0;

for G in names do
    sporadic := [];
    
    # ATLAS package stores info about character tables, centralisers etc
    chars := CharacterTable(G);
    orders := OrdersClassRepresentatives(chars);
    order_set := Set(orders);
    
    cent := SizesCentralisers(chars);
    nClasses := Length(cent);
    
    # Check all element orders
    for o in order_set do
        # Get all classes with this order
        classes := Filtered([1 .. nClasses], j -> (orders[j] = o));
        
        # Get total nof elements of this order
        prob := Sum(classes, j -> 1 / cent[j]); 
        
        # Store order, expected number of random selections to find, and
        # probability to find
        Add(sporadic, [o, Int(1 / prob + 1 / 2), prob]);
    od;
    
    Add(sporadics, 
        JoinStringsWithSeparator(["[* \"", G, "\", ", 
                String(sporadic), " *]"], ""));
od;

# Print MAGMA readable info 
Print("return [");
Print(JoinStringsWithSeparator(sporadics, ",\n"));
Print("];\n");
