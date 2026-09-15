-- grothendieckCousin(H,x) returns G, where G#q has entries y => H#y
-- for y>=x with length(y)=q. 
-- G#q records the summands N_y of GC_x^q. 

-- cousinCohomology(G) returns C, where C#q#p lists the simple labels
-- occurring in Gr^W_p H^q(G). Zero degrees and weight pieces are omitted.
-- The calculation uses the Boolean cube structure of these two cases.

-- allCousinCohomology(H) returns a table A with an entry for every x:
-- A#x = cousinCohomology(grothendieckCousin(H,x)).
-- Thus A#x#q#p lists the simple labels in Gr^W_p H^q(GC_x).


grothendieckCousin = (H, x) -> (
    if not H#?x then error "unknown index";
    G := new MutableHashTable;
    vertices := {x};
    while #vertices > 0 do (
        q := H#(first vertices)#"length";
        G#q = hashTable apply(vertices, y -> y => H#y);
        vertices = sort unique flatten apply(vertices,
            y -> values (H#y#"rightAscents"));
    );
    hashTable pairs G
);


cousinCohomology = G -> (
    degrees := new MutableHashTable;
    scan(keys G, q -> scan(values (G#q), N ->
        scan(keys (N#"weights"), p -> scan(N#"weights"#p, t -> (
            k := (p, t);
            degrees#k = append(if degrees#?k then degrees#k else {}, q);
        )))
    ));
    H := new MutableHashTable;
    scan(keys degrees, k -> if #(degrees#k) == 1 then (
        q := first (degrees#k);
        p := k#0;
        t := k#1;
        if not H#?q then H#q = new MutableHashTable;
        if not (H#q)#?p then H#q#p = {};
        H#q#p = append(H#q#p, t);
    ));
    hashTable apply(keys H, q -> q =>
        hashTable apply(keys (H#q), p -> p => sort (H#q#p)))
);


allLocalCohomology = H -> hashTable apply(keys H,
    x -> x => cousinCohomology(grothendieckCousin(H, x)));

end

restart
load "ExceptionalHermitian.m2";
load "grothendieckCousin.m2";

G6 = grothendieckCousin(E6D5, 26)
cousinCohomology(G6)

G21 = grothendieckCousin(E6D5, 21)
cousinCohomology(G21)


G7 = grothendieckCousin(E7E6, 55)
cousinCohomology(G6)

C6 = allLocalCohomology E6D5
C7 = allLocalCohomology E7E6

