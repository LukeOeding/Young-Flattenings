--pieri flattening code for arXiv

loadPackage"PieriMaps"

A = QQ[x0,x1,x2,x3,x4]
MX = pieri({5,4,3,2,1},{5,4,3,2,1},A);
diff(x0^5, MX);rank oo
> 64
diff(x0*x1*x2*x3*x4, MX);rank oo
> 1024

P = partitions(5)
L = apply(P, p-> product(#p, i-> (value(concatenate("x",toString i)))^(p_i) ))
for i to #L-1 do  print(toString L_i,rank diff(L_i , MX) );

R = QQ[x_0,x_1,x_2,x_3]
-- some degree 6 examples
M = pieri({6,4,3,2},{1,1,2,3,4,4},R);
-- start
diff(M, x_0^2*x_1^2*x_2*x_3);
rank oo
-- X_3^0
diff(M, x_0^3*x_1^2*x_2);
rank oo

-- X_1^0
diff(M, x_0^3*x_1*x_2*x_3);
rank oo


-- X_1^0 X_1^0
diff(M, x_0^4*x_2*x_3);
rank oo

-- X_3^0X_1^0
diff(M, x_0^4*x_1*x_2);
rank oo

-- X_3^0X_2X^0_1^0
diff(M, x_0^5*x_1);
rank oo


-- an example where no optimal flattening will produce the best bound on border rank

R = QQ[x_0,x_1,x_2,x_3]
time M7542 = pieri({7,5,4,2},{1,1,2,3,3,4,4},R); -- for a = (2,2,2,1) --- doesn't produce the best bound!
contract(M7542,x_0^7); rank oo
contract(M7542,x_0^2*x_1^2*x_2^2*x_3); rank oo
sub(255/15,RR)


--------- compute the lie derivative of a tableau
removeZeros = T-> (
    MT = new MutableHashTable from T;
    for ttt in keys MT do if MT#ttt ==0 then remove(MT,ttt);
    new HashTable from MT
)

LieDiff = (h,t,TT) -> (
    newT = hashTable {};
    for T in keys TT do (
    MM =hashTable {};
     for r from 0 to  #T-1 do (
	 for s from 0 to #T_r-1 do( 
             if (T#r)#s == h then( 
		 tmp = apply(T, x -> new MutableList from x);
		 (tmp#r)#s=t; -- apply the raising operator to a given box
	         tmpTerm = applyValues(straighten toList apply(tmp, tt -> toList tt), v-> v*TT#T); -- straighten result and multiply by starting coefficient
	         MM = merge( MM , tmpTerm, plus); -- merge the result to the running total
		 )
    ););
newT = merge(newT, MM, plus );
);
removeZeros(newT)
)

LieDiff(0,2,hashTable{ {{0,1,3},{1,2},{3}}=>1})


---- add a row to a tableau
hTabCat = (HP, M) ->(  --- assume the hashtable {} with no declaration is the zero tableau
    if keys HP == {} then return hashTable {};
    if keys HP =!= {} then(
    shape :=length\(keys HP)#0; 
    myTarget:= standardTableaux(#shape +1,{#M}|shape); 
    MM :=hashTable {};
	for key in keys HP do( 
	    if member({M}|key, myTarget) then MM = merge( MM, hashTable{ {M}|key => HP#key} , plus)
	    else MM = merge( MM,  applyValues(straighten( {M}|key), v->v* HP#key), plus) 
   	);
    );
    return removeZeros(MM)  --- not sure if this speeds things up or not
)

-- use the straighten command to force a list of lists to be a tableau hash table
hTabCat( hashTable {}, {0,0,2,3})
hTabCat( straighten {{0,0,0},{1,1}}, {0,0,2,3})
hTabCat(LieDiff(0,2,straighten {{0,1,3},{1,2},{3}}), {0,0,0,0})

-- convert a hash table into a matrix of a Young flattening
hashToMat = (H,A,B)->(
  M = mutableMatrix(QQ,#A,#B);
  for y in keys H do   if keys H#y != {} then for x in keys H#y do  (  M_(A#y,B#x) = (H#y)#x;);
transpose matrix M)


-- make a usual Young flattening
myMat = (start, finish, mon)->(
Lt = standardTableaux(#unique mon ,finish);
Ls = standardTableaux(#unique mon,start);
A = hashTable apply(#Ls, i-> (Ls_i,i));
B = hashTable apply(#Lt, i-> (Lt_i,i));
M = mutableMatrix(QQ,#A,#B);
for j from 0 to #A-1 do(
H = hTabCat(hashTable({Ls_j=>1} ) , mon); 
   for x in keys H do M_(j,B#x) = H#x;
   );
transpose matrix M
)

-- make pieces of Young flattenings
Ls = standardTableaux(3,{2,1});
Lt = standardTableaux(3,{4,2,1});
toString Ls
toString Lt
A = hashTable apply(#Ls, i-> (Ls_i,i));
B = hashTable apply(#Lt, i-> (Lt_i,i));

H = hashTable for ls in Ls list (ls=> LieDiff(0,2, LieDiff(0,1, hTabCat(straighten(ls), {0,0,0,0}))))
M12c =hashToMat(H,A,B)
H = hashTable for ls in Ls list  (ls => LieDiff(0,2, hTabCat(LieDiff(0,1, straighten(ls)), {0,0,0,0})))
M2c1 = hashToMat(H,A,B)
H = hashTable for ls in Ls list (ls=> LieDiff(0,1, hTabCat(LieDiff(0,2, straighten(ls)), {0,0,0,0})))
M1c2 = hashToMat(H,A,B)
H = hashTable for ls in Ls list (ls=> hTabCat( LieDiff(0,2, LieDiff(0,1,straighten(ls))), {0,0,0,0}))
Mc12 = hashToMat(H,A,B)

rank \(M12c ,M1c2, M2c1 ,Mc12) -- note that they have disjoint sources, and each has rank 2


--------------------------------------------a staircase example --- 
Ls = standardTableaux(4,{3,2,1});
Lt = standardTableaux(4,{4,3,2,1});
#Ls
#Lt
A = hashTable apply(#Ls, i-> (Ls_i,i));
B = hashTable apply(#Lt, i-> (Lt_i,i));

H = hashTable for ls in Ls list (ls=> LieDiff(0,3, LieDiff(0,2, LieDiff(0,1, hTabCat(straighten(ls), {0,0,0,0})))))
M123c =hashToMat(H,A,B)
H = hashTable for ls in Ls list  (ls =>LieDiff(0,3, LieDiff(0,2, hTabCat(LieDiff(0,1, straighten(ls)), {0,0,0,0}))))
M23c1 = hashToMat(H,A,B)
H = hashTable for ls in Ls list (ls=> LieDiff(0,3, LieDiff(0,1, hTabCat(LieDiff(0,2, straighten(ls)), {0,0,0,0}))))
M13c2 = hashToMat(H,A,B)
H = hashTable for ls in Ls list (ls=> LieDiff(0,3, hTabCat(  LieDiff(0,2, LieDiff(0,1,straighten(ls))), {0,0,0,0})))
M3c12 = hashToMat(H,A,B)

H = hashTable for ls in Ls list (ls=>  LieDiff(0,2, LieDiff(0,1, hTabCat(LieDiff(0,3,straighten(ls)), {0,0,0,0}))))
M12c3 =hashToMat(H,A,B)
H = hashTable for ls in Ls list  (ls => LieDiff(0,2, hTabCat(LieDiff(0,3,LieDiff(0,1, straighten(ls))), {0,0,0,0})))
M2c13 = hashToMat(H,A,B)
H = hashTable for ls in Ls list (ls=>  LieDiff(0,1, hTabCat(LieDiff(0,3,LieDiff(0,2, straighten(ls))), {0,0,0,0})))
M1c23 = hashToMat(H,A,B)
H = hashTable for ls in Ls list (ls=> hTabCat(  LieDiff(0,3,LieDiff(0,2, LieDiff(0,1,straighten(ls)))), {0,0,0,0}))
Mc123 = hashToMat(H,A,B)


rank\{M123c ,M13c2, M23c1 ,M3c12, M12c3 ,M1c23, M2c13 ,Mc123}

M123c -M13c2 - M23c1 +M3c12-(M12c3 -M1c23 - M2c13 +Mc123)
rank oo
-------------------------------------------------- what happens with x_0^2 x_1^2 in this case?
H= hashTable for ls in Ls list (ls=>  LieDiff(0,1, LieDiff(0,1, straighten(ls))))
hashToMat(H,A,A)
rank oo

H= hashTable for ls in Ls list (ls=>  LieDiff(0,1, LieDiff(0,1, hTabCat(straighten(ls), {0,0,0,0}))))
M11c =hashToMat(H,A,B)

H= hashTable for ls in Ls list (ls=>  LieDiff(0,1, hTabCat(LieDiff(0,1,straighten(ls)), {0,0,0,0})))
M1c1 =hashToMat(H,A,B)

H= hashTable for ls in Ls list (ls=>  hTabCat(LieDiff(0,1, LieDiff(0,1, straighten(ls))), {0,0,0,0}))
Mc11 =hashToMat(H,A,B)
rank oo
rank\{M11c,M1c1,Mc11}
rank sum {M11c,M1c1,Mc11}
M123c -M13c2 - M23c1 +M3c12-(M12c3 -M1c23 - M2c13 +Mc123)
rank oo
--------------------------------------------------

-- next try (x_0*x_1*x_2)^2
printWidth = 150
Ls = standardTableaux(3,{4,2}); netList\ Ls
Lt = standardTableaux(3,{6,4,2});
#Ls
#Lt
A = hashTable apply(#Ls, i-> (Ls_i,i));
B = hashTable apply(#Lt, i-> (Lt_i,i));

-- starting space:
hashTable for ls in Ls list (ls=> hTabCat(straighten(ls), {0,0,0,0,0,0}))
H = hashTable for ls in Ls list (ls=> LieDiff(0,2,LieDiff(0,2, LieDiff(0,1,LieDiff(0,1, hTabCat(straighten(ls), {0,0,0,0,0,0}))))))
M1122c =hashToMat(H,A,B)

-- starting space:
hashTable for ls in Ls list (ls=> hTabCat(LieDiff(0,1, straighten(ls)), {0,0,0,0,0,0}))
H = hashTable for ls in Ls list (ls=> LieDiff(0,2,LieDiff(0,2, LieDiff(0,1, hTabCat(LieDiff(0,1, straighten(ls)), {0,0,0,0,0,0})))))
M122c1 =hashToMat(H,A,B) -- odd, has 4 rows, but only 3 are linearly independent

-- starting space:
hashTable for ls in Ls list (ls=>  hTabCat(LieDiff(0,2, straighten(ls)), {0,0,0,0,0,0}))
H = hashTable for ls in Ls list (ls=> LieDiff(0,2,LieDiff(0,1, LieDiff(0,1, hTabCat(LieDiff(0,2, straighten(ls)), {0,0,0,0,0,0})))))
M112c2 =hashToMat(H,A,B)

-- starting space:
hashTable for ls in Ls list (ls=>  hTabCat(LieDiff(0,2,LieDiff(0,2, straighten(ls))), {0,0,0,0,0,0}))
H = hashTable for ls in Ls list (ls=> LieDiff(0,1, LieDiff(0,1, hTabCat(LieDiff(0,2,LieDiff(0,2, straighten(ls))), {0,0,0,0,0,0}))))
M11c22 =hashToMat(H,A,B)

-- starting space:
hashTable for ls in Ls list (ls=>  hTabCat(LieDiff(0,1,LieDiff(0,2, straighten(ls))), {0,0,0,0,0,0}))
H = hashTable for ls in Ls list (ls=> LieDiff(0,1, LieDiff(0,2, hTabCat(LieDiff(0,1,LieDiff(0,2, straighten(ls))), {0,0,0,0,0,0}))))
M12c12 =hashToMat(H,A,B)

H = hashTable for ls in Ls list (ls=> LieDiff(0,2, LieDiff(0,2, hTabCat(LieDiff(0,1,LieDiff(0,1, straighten(ls))), {0,0,0,0,0,0}))))
M22c11 =hashToMat(H,A,B)

H = hashTable for ls in Ls list (ls=> LieDiff(0,1, hTabCat(LieDiff(0,1,LieDiff(0,2,LieDiff(0,2, straighten(ls)))), {0,0,0,0,0,0})))
M1c122 =hashToMat(H,A,B)

H = hashTable for ls in Ls list (ls=> LieDiff(0,2, hTabCat(LieDiff(0,1,LieDiff(0,1,LieDiff(0,2, straighten(ls)))), {0,0,0,0,0,0})))
M2c112 =hashToMat(H,A,B)

H = hashTable for ls in Ls list (ls=> hTabCat(LieDiff(0,1,LieDiff(0,1,LieDiff(0,2,LieDiff(0,2, straighten(ls))))), {0,0,0,0,0,0}))
Mc1122 =hashToMat(H,A,B)



trueM = myMat({4,2},{6,4,2},{0,0,1,1,2,2});
rank trueM

newM  = M1122c -2*(M122c1 +M112c2) + (M11c22 + 4*M12c12 +M22c11) -2*( M1c122 + M2c112) +Mc1122;

24*15*trueM - newM

rank\ {M1122c,M122c1,M112c2,M11c22,M12c12,M22c11,M1c122,M2c112,Mc1122}

--- try another staircase
Ls = standardTableaux(4,{3,2,1}); --netList\ Ls
Lt = standardTableaux(4,{4,3,2,1}); --netList\ Lt
#Ls
#Lt
A = hashTable apply(#Ls, i-> (Ls_i,i));
B = hashTable apply(#Lt, i-> (Lt_i,i));
M123c = hashToMat( hashTable for ls in Ls list (ls=> LieDiff(0,3, LieDiff(0,2,LieDiff(0,1, hTabCat(straighten(ls), {0,0,0,0}))))), A,B)
rank oo
M12c3 = hashToMat( hashTable for ls in Ls list (ls=> LieDiff(0,2, LieDiff(0,1, hTabCat(LieDiff(0,3,straighten(ls)), {0,0,0,0})))), A,B)
rank oo
M13c2 = hashToMat( hashTable for ls in Ls list (ls=> LieDiff(0,3, LieDiff(0,1, hTabCat(LieDiff(0,2,straighten(ls)), {0,0,0,0})))), A,B)
rank oo
M23c1 = hashToMat( hashTable for ls in Ls list (ls=> LieDiff(0,3, LieDiff(0,2, hTabCat(LieDiff(0,1,straighten(ls)), {0,0,0,0})))), A,B)
rank oo
M1c23 = hashToMat( hashTable for ls in Ls list (ls=> LieDiff(0,1, hTabCat(LieDiff(0,2, LieDiff(0,3,straighten(ls))), {0,0,0,0}))), A,B)
rank oo
M2c13 = hashToMat( hashTable for ls in Ls list (ls=> LieDiff(0,2, hTabCat(LieDiff(0,1, LieDiff(0,3,straighten(ls))), {0,0,0,0}))), A,B)
rank oo
M3c12 = hashToMat( hashTable for ls in Ls list (ls=> LieDiff(0,3, hTabCat(LieDiff(0,1, LieDiff(0,2,straighten(ls))), {0,0,0,0}))), A,B)
rank oo
Mc123 = hashToMat( hashTable for ls in Ls list (ls=> hTabCat(LieDiff(0,3,LieDiff(0,2, LieDiff(0,1,straighten(ls)))), {0,0,0,0})), A,B)
rank oo
trueM = myMat({3,2,1},{4,3,2,1},{0,1,2,3}); rank oo
-24*trueM + M123c - M12c3 - M13c2 - M23c1 + M1c23 + M2c13 + M3c12 - Mc123

---- use this same flattening for the monomial x_0^2 *x_1^2
M11c = hashToMat( hashTable for ls in Ls list (ls=> LieDiff(0,1, LieDiff(0,1, hTabCat( straighten(ls), {0,0,0,0})))), A,B)
rank oo
M1c1= hashToMat( hashTable for ls in Ls list (ls=> LieDiff(0,1,  hTabCat(LieDiff(0,1,straighten(ls)), {0,0,0,0}))), A,B)
rank oo
Mc11 = hashToMat( hashTable for ls in Ls list (ls=>  hTabCat(LieDiff(0,1, LieDiff(0,1,straighten(ls))), {0,0,0,0})), A,B)
rank oo

M11c + M1c1 + Mc11
rank oo
--- optimal shape for the monomial x_0^2 *x_1^2
Ls = standardTableaux(2,{2}); --netList\ Ls
Lt = standardTableaux(2,{4,2}); --netList\ Lt
#Ls
#Lt
A = hashTable apply(#Ls, i-> (Ls_i,i));
B = hashTable apply(#Lt, i-> (Lt_i,i));
M11c = hashToMat( hashTable for ls in Ls list (ls=> LieDiff(0,1, LieDiff(0,1, hTabCat( straighten(ls), {0,0,0,0})))), A,B)
rank oo
M1c1= hashToMat( hashTable for ls in Ls list (ls=> LieDiff(0,1,  hTabCat(LieDiff(0,1,straighten(ls)), {0,0,0,0}))), A,B)
rank oo
Mc11 = hashToMat( hashTable for ls in Ls list (ls=>  hTabCat(LieDiff(0,1, LieDiff(0,1,straighten(ls))), {0,0,0,0})), A,B)
rank oo

M11c + M1c1 + Mc11
rank oo


--- try one where the contragradient isn't quite right... x_0^2*x_1^2*x_2*2*x_3
Ls = standardTableaux(4,{5,4,2}); --netList\ Ls
Lt = standardTableaux(4,{7,5,4,2}); --netList\ Lt
#Ls
#Lt
A = hashTable apply(#Ls, i-> (Ls_i,i));
B = hashTable apply(#Lt, i-> (Lt_i,i));
time M11223c = hashToMat( hashTable for ls in Ls list (ls=> LieDiff(0,3, LieDiff(0,2,LieDiff(0,2,LieDiff(0,1,LieDiff(0,1, hTabCat(hashTable{ls=>1}, {0,0,0,0,0,0,0})))))) 	) , A,B);
-- took 4694s, and produced a matrix of rank 12.
time M1122c3 = hashToMat( hashTable for ls in Ls list (ls=> LieDiff(0,2,LieDiff(0,2,LieDiff(0,1,LieDiff(0,1, hTabCat(LieDiff(0,3,hashTable{ls=>1}), {0,0,0,0,0,0,0}))))) 	) , A,B);
rank M1122c3
-- took 6578s, and produced a matrix of rank 12.


--- now compute the partial flattenings for this case


time Pc11223 = hashToMat( hashTable for ls in Ls list (ls=>  hTabCat(LieDiff(0,3,LieDiff(0,2,LieDiff(0,2,LieDiff(0,1,LieDiff(0,1, hashTable{ls=>1}))))), {0,0,0,0,0,0,0}) 	) , A,B);
time P1c1223 = hashToMat( hashTable for ls in Ls list (ls=>  hTabCat(LieDiff(0,3,LieDiff(0,2,LieDiff(0,2,LieDiff(0,1, hashTable{ls=>1})))), {0,0,0,0,0,0,0}) 	) , A,B);
time P11c223 = hashToMat( hashTable for ls in Ls list (ls=>  hTabCat(LieDiff(0,3,LieDiff(0,2,LieDiff(0,2, hashTable{ls=>1}))), {0,0,0,0,0,0,0}) 	) , A,B);

time P2c1123 = hashToMat( hashTable for ls in Ls list (ls=>  hTabCat(LieDiff(0,3,LieDiff(0,2,LieDiff(0,1,LieDiff(0,1, hashTable{ls=>1})))), {0,0,0,0,0,0,0}) 	) , A,B);
time P12c123 = hashToMat( hashTable for ls in Ls list (ls=>  hTabCat(LieDiff(0,3,LieDiff(0,2,LieDiff(0,1, hashTable{ls=>1}))), {0,0,0,0,0,0,0}) 	) , A,B);
time P112c23 = hashToMat( hashTable for ls in Ls list (ls=>  hTabCat(LieDiff(0,3,LieDiff(0,2, hashTable{ls=>1})), {0,0,0,0,0,0,0}) 	) , A,B);

time P22c113 = hashToMat( hashTable for ls in Ls list (ls=>  hTabCat(LieDiff(0,3,LieDiff(0,1,LieDiff(0,1, hashTable{ls=>1}))), {0,0,0,0,0,0,0}) 	) , A,B);
time P122c13 = hashToMat( hashTable for ls in Ls list (ls=>  hTabCat(LieDiff(0,3,LieDiff(0,1, hashTable{ls=>1})), {0,0,0,0,0,0,0}) 	) , A,B);
time P1122c3 = hashToMat( hashTable for ls in Ls list (ls=>  hTabCat(LieDiff(0,3,hashTable{ls=>1}), {0,0,0,0,0,0,0})) , A,B);

time P3c1122 = hashToMat( hashTable for ls in Ls list (ls=>  hTabCat(LieDiff(0,2,LieDiff(0,2,LieDiff(0,1,LieDiff(0,1, hashTable{ls=>1})))), {0,0,0,0,0,0,0}) 	) , A,B);
time P13c122 = hashToMat( hashTable for ls in Ls list (ls=>  hTabCat(LieDiff(0,2,LieDiff(0,2,LieDiff(0,1, hashTable{ls=>1}))), {0,0,0,0,0,0,0}) 	) , A,B);
time P113c22 = hashToMat( hashTable for ls in Ls list (ls=>  hTabCat(LieDiff(0,2,LieDiff(0,2, hashTable{ls=>1})), {0,0,0,0,0,0,0}) 	) , A,B);

time P23c112 = hashToMat( hashTable for ls in Ls list (ls=>  hTabCat(LieDiff(0,2,LieDiff(0,1,LieDiff(0,1, hashTable{ls=>1}))), {0,0,0,0,0,0,0}) 	) , A,B);
time P123c12 = hashToMat( hashTable for ls in Ls list (ls=>  hTabCat(LieDiff(0,2,LieDiff(0,1, hashTable{ls=>1})), {0,0,0,0,0,0,0}) 	) , A,B);
time P1123c2 = hashToMat( hashTable for ls in Ls list (ls=>  hTabCat(LieDiff(0,2, hashTable{ls=>1}), {0,0,0,0,0,0,0}) 	) , A,B);

time P223c11 = hashToMat( hashTable for ls in Ls list (ls=>  hTabCat(LieDiff(0,1,LieDiff(0,1, hashTable{ls=>1})), {0,0,0,0,0,0,0}) 	) , A,B);
time P1223c1 = hashToMat( hashTable for ls in Ls list (ls=>  hTabCat(LieDiff(0,1,hashTable{ls=>1}), {0,0,0,0,0,0,0})    ) , A,B);
time P11223c = hashToMat( hashTable for ls in Ls list (ls=>  hTabCat(hashTable{ls=>1}, {0,0,0,0,0,0,0}) ) , A,B);

-----
rank\{ Pc11223, P1c1223, P11c223, P2c1123, P12c123, P112c23, P22c113, P122c13, P1122c3, P3c1122, P13c122, P113c22, P23c112, P123c12, P1123c2, P223c11, P1223c1, P11223c}