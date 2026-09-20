
-- Uses the tables in ExceptionalHermitian.m2 to calculate
-- local cohomology and HRH via the Grothendieck--Cousin complex



grothendieckCousin = (H, x) -> (
-- Let H be one of the two hash tables from ExceptionalHermitian.m2.
-- grothendieckCousin(H,x) returns a hash table G, where G#q has entries y => H#y
-- for y>=x with length(y)=q. 
-- G#q records the summands N_y of GC_x^q. 
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
-- G is the output of grothendieckCousin(H,x)    
-- cousinCohomology(G) returns a hash table C, where C#q#p lists the simple labels
-- occurring in Gr^W_p H^q(G). 
-- The calculation uses Theorem 3.1 in 
-- "Local cohomology with Schubert support on compact Hermtian symmetric spaces"
-- in order to describe the maps in G.
-- In short, the maps are "maximal rank" as allowed by the Bruhat order
-- and the composition factors of the dual Verma modules.
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


-- Let H be one of the two hash tables from ExceptionalHermitian.m2.
-- allCousinCohomology(H) returns a hash table A with an entry for every x:
-- A#x = cousinCohomology(grothendieckCousin(H,x)).
-- Thus A#x#q#p lists the simple labels in Gr^W_p H^q(GC_x).
allCousinCohomology = H -> hashTable apply(keys H,
    x -> x => cousinCohomology(grothendieckCousin(H, x)));


hrh = (H, x) -> (
-- H is one of the two hash tables from ExceptionalHermitian.m2. 
-- x is a coset representative of W/W_m  
 -- this function calculates the Hodge rational homology level of
-- Dirks--Olano--Raychaudhury and Park--Popa.
-- It does this by using cousinCohomology and Lemma 2.1 of
-- "Hodge ideals for the determinant hypersurface" by Perlman--Raicu,
-- which describes the starting level of F on IC_Z^H(k).
-- Precisely, an additional constituent $(q,p;y)$ 
-- starts in Hodge level $(d_X+\ell(y)-p)/2$. 
-- The function hrh takes the minimum minus one, excluding the lowest weight piece   
    C := cousinCohomology(grothendieckCousin(H, x));
    d := max apply(values H, N -> N#"length");
    c := H#x#"length";
    h := infinity;
    scan(keys C, q -> scan(keys (C#q), p -> if p > d+c then
        scan(C#q#p, y -> h = min(h, (d + H#y#"length" - p)//2 - 1))
    ));
    h
);

-- allHRH(H) takes a hash table H from ExceptionalHermitian.m2.
-- and outputs a hash table of all HRH levels.
allHRH = H -> hashTable apply(keys H, x -> x => hrh(H, x));


end

restart
load "ExceptionalHermitian.m2";
load "grothendieckCousin.m2";

G6 = grothendieckCousin(E6D5, 26)
cousinCohomology(G6)

G21 = grothendieckCousin(E6D5, 21)
cousinCohomology(G21)


G7 = grothendieckCousin(E7E6, 55)
cousinCohomology(G7)

C6 = allCousinCohomology E6D5
C7 = allCousinCohomology E7E6

hrh(E6D5, 20) -- 2
hrh(E7E6, 39) -- 3
allHRH(E6D5)
allHRH(E7E6)
