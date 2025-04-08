Exists:=function(list, func)
    #returns true if there exists an element in list such that func(element)=true
    local l;
    for l in list do if func(l)=true then return true; fi; od;
    return false;
end;

isRepFrobenius:=function(G, r, p)
    #returns false if there exists a non-trivial element in G such that 1 is an eigenvalue of x^representation 
    return not Exists(G, x->not x=x^0 and Z(p)^0 in Eigenvalues(GF(p), x^r));
end;

maxCoprimeFactor:=function(m, p)
    #returns the maximum coprime factor of m with p
    return Maximum(Filtered(DivisorsInt(m), x->Gcd([x,p])=1));
end;

semidirectGroupRepresentation:=function(G, chi, p)
    #returns the semidirect product of K\rtimes G where K is the irreducible F_pG-module and the action is given by chi
    local gens, MatrixGroup, dim;
    gens:=GeneratorsOfGroup(G);
    #this computes the dimension of the representation
    dim:=Size(gens[1]^chi);
    MatrixGroup:=Group(List(gens, x->x^chi));
    return SemidirectProduct(MatrixGroup, GF(p)^dim);
end;

isRepkEigenvalue:=function(G, r, p,k)
    #retruns true if the k-eigenvalue property holds for the representation of G
    #k-eigenvalue property of a G-module V holds if for all v in V there exists g in G and mu in GF(p) of order k such that g^r*v=mu*v
    local dim, V, mu;
    dim:=Size(G.1^r);
    V:=FullRowSpace(GF(p), dim);
    #pick an element of order k in GF(p)
    mu:=Filtered(GF(p), x->Order(x)=k)[1];
    return ForAll(V, v->Exists(G, g->g^r*v=mu*v));
end;

isRepSemirational:=function(G, r, p)
    #the representation is "semi-rational" if (p-1)/2-eigenvalue property holds
    return isRepkEigenvalue(G,r,p, (p-1)/2);
end;

IrreducibleRepFrobeniusFaithfulSemirational:=function(G,p)
    #returns the irreducible representations of G that are Frobenius and semirational
    local I;
    I:=IrreducibleRepresentations(G, GF(p));
    I:=Filtered(I, r->isRepFrobenius(G, r, p) and isRepSemirational(G, r, p));
    return Filtered(I, chi->maxCoprimeFactor(
    Size(semidirectGroupRepresentation(G, chi, p)), p)=Size(G));
end;

fieldCharacters:=function(G)
    #returns the field of values of every irreducible (complex) character of G
    return List(Irr(G), x->Field(Rationals, x));
end;

IsrSR:=function(G, r)
    #this function checks if the group G is r-semi-rational
    #In particular, it checks if the field of values of every irreducible character of G intersects trivially the field fixed by the Galois automorphism \sigma_r
    #and if every field of values of every irreducible character of G has degree at most 2 over the rationals.
    local n, U, F;
    n:=Exponent(G);
    U:=Units(ZmodnZ(n));
    F:=NF(n, List(Subgroup(U, [ZmodnZObj(r,n)]), x->Int(x)));
    return ForAll(fieldCharacters(G), f->Intersection(f, F)=Rationals and DegreeOverPrimeField(f)<=2);
end;

USRInt:=function(G)
    #returns the semi-rationality of G, i.e. the set of integers r such that the group G is r-semi-rational
    local n, U;
    n:=Exponent(G);
    U:=List(Units(ZmodnZ(n)), x->Int(x));
    return Filtered(U, k->IsrSR(G,k));
end;

remInt:=function(n,m)
    if RemInt(n,m)>m/2 then return RemInt(n,m)-m;
    else return RemInt(n,m); fi;
end;

pIrreducibleSemidirectFrobeniusFaithfulSemirational:=function(G,p)
    #returns the semidirect product of K\rtimes G where K is the irreducible F_pG-module and the action is Frobenius
    local I, IF, ISemiDirectFrobenius;
    I:=IrreducibleRepresentations(G, GF(p));
    #frobenius representations
    IF:=Filtered(I, r->isRepFrobenius(G, r, p) and isRepSemirational(G, r, p));
    #semidirect product of frobenius representations
    ISemiDirectFrobenius:=List(IF, chi->semidirectGroupRepresentation(G, chi, p));
    return Filtered(ISemiDirectFrobenius, x->maxCoprimeFactor(Size(x), p)=Size(G));
end;


extensionsSG:=function(G,p)
    #returns the (eventual) semi-rationality of K^n\rtimes G where K is the irreducible F_pG-module and the action is given by chi
    #and the action is both Frobenius and sem-irational.
    local I, i, x, l, eigenValues, res, chi, dim, SG, r, rat,el, ordersel;
    res:=[];
    I:=IrreducibleRepFrobeniusFaithfulSemirational(G,p);
    #since, even if we have more than one representation, the semidirect product is isomorphic to each other, we can take the first one
    SG:=USRInt(pIrreducibleSemidirectFrobeniusFaithfulSemirational(G,p)[1]);
    chi:=I[1];
    dim:=Size(G.1^chi);
    #we want to compute the numbers in [0..p-1] such that there exist an element x in G such that x^chi=i*(x^0)^chi
    eigenValues:=Filtered([0..p-1], i->Exists(G, y->y^chi=i*(y^0)^chi));
    eigenValues:=List(eigenValues, x->ZmodnZObj(x,p));
    #cAct:=List(Filtered(List(G, y->Filtered([0..p-1], i->y^chi=i*(y^0)^chi)), el->not el=[]), eel->eel[1]);
    for r in SG do
        l:=[];
        Add(l, ZmodnZObj(r,p));
        Append(l, eigenValues);
        #we are verifying (2) of Lemma 4.9 where Group(l)=Z_G(x)<tau_r> and Group(eigenValues)=Z_G(x)
        #observe that Z_G(x) does not depend on the non-trivial element x of G
        if Size(Group(l))=p-1 and Size(Group(eigenValues)) in [p-1, (p-1)/2] then 
            Add(res, r);
        fi;
    od;
    #in order to display the result we want to compute the order of the elements in the semi-rationality
    #and compute the rationality.
    rat:=[];
    el:=List(res, x->ZmodnZObj(x,Exponent(G)*p));
    ordersel:=List(el, x->Order(x));
    #we can remove remInt 
    res:=List(res, x->remInt(x, Exponent(G)*p));
    rat:=List(el, x->remInt(Int(el[1]^-1*x), Exponent(G)*p));
    return [res, ordersel, rat];
end;

#this function computes the N_G((v,w)) where (v,w) in VxW V is the first irreducible F_pG-module Frobenius semi-rational and W is the second one
#clearly, if the size of the output < (p-1)/2 the element (v,w) cannot be semi-rational and therefore, VxW \rtimes G cannot be semi-rational too

counterExample:=function(G,p, v, w)
    local I, U;
    U:=Units(ZmodnZ(Exponent(G)));
    I:=IrreducibleRepFrobeniusFaithfulSemirational(G,p);
    if not Size(I)=2 then
        #we have to check only if we have more than one representation
        #we know that in those cases appear only two irreducible representations with same dimension
        return false;
    fi;
    #we need to find the elements in G such that normalize v , w and acts as the multiplication of the same constant
    return Filtered(G, x->Exists(ZmodnZ(p), i->x^I[1]*v=i*v and x^I[2]*w=i*w));
    #return Filtered(G, x->ForAll(I, rep->x^rep*v in Lv and x^rep*w in Lw and x^rep*(v-w) in Lvw) );
end;




