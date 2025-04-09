computations:=function()
local listTable1, listTable2, el, H, p, ext, I, SG, SGUnits, rat, ordersel, listExtendedG;
#Starting from Table 1 we check the existence of G=K\rtimes H such that G is quadratic rational.
#and K is an irreducible F_pH-module (we test the (p-1)/2 -eigenvalue property).
#In this list we present the IdGroup of the complement H and the characteristic p.
listTable1:=[   
    [ [ 2, 1 ], 3 ], 
    [ [ 2, 1 ], 5 ], 

    [ [ 4, 1 ], 3 ], 
    [ [ 4, 1 ], 5 ], 
    
    [ [ 6, 2 ], 5 ], 
    [ [ 6, 2 ], 7 ],
    [ [ 6, 2 ], 13 ], 
    
    [ [ 8, 4 ], 3 ], 
    [ [ 8, 4 ], 5 ], 
    
    [ [ 12, 1 ], 5 ], 
    [ [ 12, 1 ], 7 ], 
    [ [ 12, 1 ], 13 ],

    [ [ 16, 9 ], 3 ], 
    [ [ 16, 9 ], 5 ], 
    
    [ [ 20, 1 ], 3 ], 
    
    [ [ 24, 3 ], 5 ], 
    [ [ 24, 3 ], 7 ], 
    [ [ 24, 3 ], 13 ],

    [ [ 24, 4 ], 5 ], 
    [ [ 24, 4 ], 7 ], 
    [ [ 24, 4 ], 13 ], 
    
    [ [ 24, 11 ], 5 ], 
    [ [ 24, 11 ], 7 ], 
    [ [ 24, 11 ], 13 ],

    [ [ 48, 18 ], 5 ], 
    [ [ 48, 18 ], 7 ], 
    [ [ 48, 18 ], 13 ], 
    
    [ [ 48, 28 ], 5 ], 
    [ [ 48, 28 ], 7 ], 
    [ [ 48, 28 ], 13 ],

    [ [ 120, 5 ], 7 ], 
    [ [ 120, 5 ], 11 ], 
    [ [ 120, 5 ], 13 ], 
    
    [ [ 240, 89 ], 7 ], 
    [ [ 240, 89 ], 11 ],
    [ [ 240, 89 ], 13 ], 
    [ [ 240, 89 ], 17 ] ];

#In Theorems 5.1--5.4 we claim that the result is the following.
#Each item of the previous list is here presented together with the relevant semi-rationality and rationality.
#If the group G=K\rtimes H is not uniformly semi-rational, this datas are set to 0 and [].

listTable2:=[
    [[2,1], 3, 1,[-1]],         #rational
    [[2,1], 5, 3, [-1]], 

    [[4,1], 3, -1, [5]], 
    [[4,1], 5, -1, [13]], 

    [[6,2], 5, -7, [19]], 
    [[6,2], 7, -1, [19]],
    [[6,2], 13, -7, [49]],

    [[8,4], 3, 1, [5, -1]],     #rational 
    [[8,4], 5, 1, [17, -1]],    #rational

    [[12,1], 5, -1, [17,41]], 
    [[12,1], 7, 0, []],         #not USR
    [[12,1], 13, 0, []],        #not USR

    [[16,9], 3, 5, [7,23]],
    [[16,9], 5, 3, [31, 9]],

    [[20,1], 3, 7, [41, 49]],

    [[24,3], 5, -1, [7, 19] ],
    [[24,3], 7, -1, [13, 19]],
    [[24,3], 13, 0, []],         #not USR

    [[24,4], 5, 7, [11, 49]],
    [[24,4], 7, 0, []],          #not USR
    [[24,4], 13, 0, []],         #not USR

    [[24,11], 5, -7, [19, -11]],
    [[24,11], 7, -1, [19, 43]],
    [[24,11], 13, -7, [49, 79]],

    [[48,18], 5, -13, [31, 49]],
    [[48,18], 7, 0, []],         #not USR
    [[48,18], 13, 0, []],        #not USR    

    [[48,28], 5, -13, [31, 41, 49]],
    [[48,28], 7, 5, [73, 113, 127]],
    [[48,28], 13, 0, []],        #not USR

    [[120,5], 7, 0, []],         #not USR
    [[120,5], 11, -7, [541, 529, 221, 331]],
    [[120,5], 13, 0, []],        #not USR

    [[240, 89], 7, 0, []],          #not USR
    [[240, 89], 11, 0, []],         #not USR
    [[240, 89], 13, 0, []],         #not USR
    [[240, 89], 17, 0, []]          #not USR
];

#We test listTable2.
for el in listTable2 do 
    H:=SmallGroup(el[1]);
    p:=el[2];
    I:=IrreducibleRepFrobeniusFaithfulSemirational(H,p);
    if Size(I)=0 then 
        Print("The group ", StructureDescription(H), " has NO semi-rational Frobenius representation over GF(", p ,") \n\n\n");
    else
        Print("The group ", StructureDescription(H), " has ", Size(I), " semi-rational Frobenius representation(s) over GF(", p ,") of dimension ", List(I, rep->Size(H.1^rep)) ," \n\n\n");
        #this function computes the semi-rationality of G 
        SG:=USRInt(pIrreducibleSemidirectFrobeniusFaithfulSemirational(H,p)[1]);
        SG:=List(SG, x->remInt(x, Exponent(H)*p));
        SGUnits:=List(SG, x->ZmodnZObj(x,Exponent(H)*p));
        rat:=List(SGUnits, x->remInt(Int(SGUnits[1]^-1*x), Exponent(H)*p));
        ordersel:=List(SGUnits, x->Order(x));
        Print("Semirationality=", SG, " and ", el[3] ," in SG", el[3] in SG ,"\n");
        Print("Orders= ", ordersel, "\n");
        Print("Rationality=", rat, "\n" );

        Print("The rationality is generated by ", el[4], " is ", Group(List(rat, x->ZmodnZObj(x, Exponent(H)*p)))=Group(List(el[4], x->ZmodnZObj(x, Exponent(H)*p)))  ,  "\n\n\n");
    fi;
od;

#Next, we check the claim of Theorems 5.1--5.4 for the groups G_n constructed from G as above.
listExtendedG:=[ 
    [ [ 2, 1 ], 3, 1, [ -1 ] ],     #rational
    [ [ 2, 1 ], 5, 3, [ -1 ] ], 

    [ [ 4, 1 ], 3, -1, [ 5 ] ], 
    [ [ 4, 1 ], 5, -1, [ 13 ] ],

    [ [ 6, 2 ], 5, -7, [ 19 ] ], 
    [ [ 6, 2 ], 7, -1, [ 19 ] ], 
    [ [ 6, 2 ], 13, -7, [ 49 ] ], 

    [ [ 8, 4 ], 3, 1, [ 5, -1 ] ],      #rational
    [ [ 8, 4 ], 5, 3, [ 9, 11 ] ],      #G_n different from G_1

    [ [ 12, 1 ], 5, 7, [ 29, 41 ] ],    #G_n different from G_1

    [ [ 16, 9 ], 3, 5, [ 7, 23 ] ], 
    [ [ 16, 9 ], 5, 3, [ 31, 9 ] ],

    [ [ 20, 1 ], 3, 7, [ 41, 49 ] ], 

    [ [ 24, 3 ], 5, -7, [ 19, 49 ] ],  #G_n different from G_1
    [ [ 24, 3 ], 7, 0, [  ] ],         #G_n is not uniformly semi-rational

    [ [ 24, 4 ], 5, 7, [ 11, 49 ] ],  

    [ [ 24, 11 ], 5, -7, [ 19, -11 ] ], 
    [ [ 24, 11 ], 7,  -1, [ 19, 43 ] ],
    [ [ 24, 11 ], 13, -7, [ 49, 79 ] ], 

    [ [ 48, 18 ], 5, -13, [ 31, 49 ] ],

    [ [ 48, 28 ], 5, -13, [ 31, 41, 49 ] ],
    [ [ 48, 28 ], 7, [  ] ],          #G_n is not uniformly semi-rational

    [ [ 120, 5 ], 11, [  ] ] ];        #G_n is not uniformly semi-rational

#We test listExtendedG using condition (2) of Lemma 4.9 on G (see fifth paragraph on page 19).
for el in listExtendedG do
    H:=SmallGroup(el[1]);
    p:=el[2];
    ext:=extensionsSG(H, p);
    if ext[1]=[] then
        Print("The GF(", p, ") module of ", StructureDescription(H), " DOES NOT extend\n");
    else
        Print("The GF(", p, ") module of ", StructureDescription(H), " extends as follows\n");
        Print("Semi-rationality=", ext[1], " and ", el[3], " in SG is", el[3] in ext[1], "\n");
        Print("Orders of elements in semi-rationality=", ext[2], "\n");
        Print("Rationality=", ext[3], "\n");
        Print("The rationality is generated by ", el[4], " = ", Group(List(ext[3], x->ZmodnZObj(x, Exponent(H)*p)))=Group(List(el[4], x->ZmodnZObj(x, Exponent(H)*p)))  ,  "\n\n\n");
        Print("\n\n\n");
    fi;
od;

#Finally we discard the remaining non-homogeneous cases (see fourth paragraph on page 19)
checkingRemainingCases();

end;
