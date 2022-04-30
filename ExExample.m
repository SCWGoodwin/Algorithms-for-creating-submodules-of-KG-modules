//This file produces the module described in Ivanyos-Lux section 5
//This example takes a long time to solve with the Holt-Rees algorithm. 
//ConstructModule(n,p^k) will produce a module over GF(p) of dimension k*n
ConstructModule:=function(n,q) 
   K:=GF(q);
   F:=PrimeField(K);
   L:=MatrixAlgebra(K,n);
   A:=L!SL(n,q).1;
   B:=L!SL(n,q).2;
   // Fro(A) is defined in Frobenius.m 
   // it applies the Frobenius morphism to each entry of A.
   // AF:=Fro(A);
   // BF:=Fro(B);
   AF := FrobeniusImage (A, 1);
BF := FrobeniusImage (B, 1);
I:=Identity(L);Z:=Zero(L);
   a:=BlockMatrix(2,2,[A,I,Z,AF]);
   b:=BlockMatrix(2,2,[B,I,Z,BF]);
   G,f:=WriteOverSmallerField(GL(2*n,q),F);
   a:=f(a);
   b:=f(b);
   A:=a;
   B:=b;
   m:=NumberOfRows(a);
   for i in [1..10] do
      c:=a*b*a*b*b*a*b*a*b*a*b*b*a*b*b;
      d:=a*b*a*b*b*a*b*b*a*b*a*b*a*b*b;
      a:=c; b:=d;
   end for;
   G:=MatrixGroup<m,F|c,d>;
   G:=RandomConjugate(G);
   M:=GModule(G);
   return M,A,B;
end function;
Profile:=function(n,q,m)
   timesmeat:=[];
   timesmeatil:=[];
   timesmeatlg:=[];
   iterationsmeat:=[];
   iterationsmeatil:=[];
   for i in [1..m] do
      M:=ConstructModule(n,q);
      T:=Time(); L,_,num:=Meat(M:limit:=10^9); t:=Time(T); Append(~timesmeat,t); Append(~iterationsmeat,num);
      T:=Time(); L,_,num:=MeatIL(M); t:=Time(T); Append(~timesmeatil,t); Append(~iterationsmeatil,num);
      T:=Time(); L:=MeatLG(M); t:=Time(T); Append(~timesmeatlg,t);
   end for;
   return timesmeat,timesmeatil,timesmeatlg,iterationsmeat,iterationsmeatil;
end function;
