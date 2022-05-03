SeedLength := 10;

/* preprocessing for seed */

procedure ScrambleElements (~gens, n)

   NmrGens := #gens;

   for i in [1..n] do
      s := Random ([1..NmrGens - 1]);
      t := Random ([1..NmrGens - 1]);
      if s ne t then 
         u := Random ([1,2,3]);
         if u eq 1 then 
            elt := gens[s] * gens[t];
         elif u eq 2 then 
            elt := gens[t] * gens[s];
         elif u eq 3 then 
            elt := gens[s] + gens[t];
         end if;
         if elt ne 0 then
               gens[s] := elt;
         end if;
      end if;
      v := Random ([1,2]);
      if v eq 1 then 
         elt2:= gens[NmrGens] * gens[s];
      else
         elt2:= gens[NmrGens] + gens[s];
      end if;
      if elt2 ne 0 then
         gens[NmrGens] :=elt2;
      end if;
   end for; 

end procedure; 

/* initialise seed for generating random elements */
     
procedure InitialiseSeed (G, SeedLength, n)

   if assigned G`Seed then return; end if;
   gens := [Generic (G) ! G.i: i in [1..Ngens (G)]];
   NmrGens := #gens;
   if #gens ne 0 then
      Length := Maximum (SeedLength, #gens + 1);
      Seed := [gens[i mod NmrGens + 1] : i in [1..Length]];
      ScrambleElements (~Seed, n);
   else 
      Seed := [Identity (G): i in [1..2]];
   end if;

   G`Seed := Seed;

end procedure;

/* construct a random element */

RandomElement := function (G, NumberMultiplications) 

   InitialiseSeed (G, SeedLength, NumberMultiplications);
   ScrambleElements (~G`Seed, 1);
   return G`Seed[#G`Seed];

end function; 

Meat:= function(M: NumberMultiplications := 25, limit := 100)
//The Holt-Rees Meataxe as described in Testing modules for irreducibility, 1994.
//After testing limit number of random elements of A, this will terminate
//with error message and will return M. To allow any number of attempts, set
//limit to 0.
   K := Field(M);
   d := Dimension(M);
   A := Action(M);

   gen := Generators(A);
   ATgen:={Transpose(a):a in gen};

   num := 0;
   while num lt limit or limit eq 0 do

      num := num+1;
      r := RandomElement(A,NumberMultiplications);
      f := CharacteristicPolynomial(r);
      F := Factorization(f);

      for i in [1..#F] do

         p := F[i][1];
         x := Evaluate(p,r);
         N := NullSpace(x);
         v := BasisElement(N,1);
         L := sub<M|v>;

         if Dimension(L) lt Dimension(M) then
            return L,2,num;
         end if;

         if Dimension(N) eq Degree(p) then

            xT := Transpose(x);
            NT := Nullspace(xT);
            vT := BasisElement(NT,1);
            GT := MatrixGroup<d,K|ATgen>;
            MT := GModule(GT);
            LT := sub<MT|vT>;

            if Dimension(LT) lt d then

               V := VectorSpace(K,d);
               B := {V!v:v in Basis(MT)};
               WT := sub<V|B>;
               W := OrthogonalComplement(V,WT);
               L := sub<M|BasisElement(W,1)>;
               return L,3,num;

            end if;

            return M,1,num;

         end if;
      end for;
      
   end while;
   print("Failed to decide before limit.");
   return M,0,num;
end function;

// This function carries out the operations described in 
// 3(i),(ii) of Ivanyos-Lux.
ILAlgorithm:=function(r,c,p,l,A,M,NumberMultiplications)
   q:=c div p^l;
   _,_,b:=XGCD(p^l,q);
   i:=b*q mod c;
eta := RandomElement(A,NumberMultiplications);
   v:=Random(M);
   y:=Evaluate(i,r)*eta*Evaluate(i,r);
   z:=r*y-y*r;
   return sub<M|v*z>;
end function;

// MeatIL is the Holt-Rees Meataxe with the Ivanyos-Lux extension. 
// It returns the following extra values if a submodule is found: 
// 1,2 - the two ways the Holt-Rees algorithm can find a submodule. 
// 3 - If the algorithm found a submodule using the Ivanyos-Lux extension. 
// The second number is the number of random elements chosen.
MeatIL:= function(M: NumberMultiplications := 25, limit := 100)

   K := Field(M);
   d := Dimension(M);
   A := Action(M);

   gen := Generators(A);
   ATgen:={Transpose(a):a in gen};

   num := 0;

   while num lt limit or limit eq 0 do

      num := num+1;
      r := RandomElement(A,NumberMultiplications);
      f := CharacteristicPolynomial(r);
      F := Factorization(f);
      l:=Minimum({F[i][2]:i in [1..#F]});
      Min:=[x:x in F|x[2] eq l];

      N := ILAlgorithm(r,f,Min[1][1],l,A,M,NumberMultiplications);

      if Dimension(N) gt 0 and Dimension(N) lt Dimension(M) then

         return N,4,num;

      end if;

//The below section is the same as Meat(M).

      for i in [1..#F] do

         p := F[i][1];
         x := Evaluate(p,r);
         N := NullSpace(x);
         v := BasisElement(N,1);
         L := sub<M|v>;

         if Dimension(L) lt Dimension(M) then
            return L,2,num;
         end if;

         if Dimension(N) eq Degree(p) then

            xT := Transpose(x);
            NT := Nullspace(xT);
            vT := BasisElement(NT,1);
            GT := MatrixGroup<d,K|ATgen>;
            MT := GModule(GT);
            LT := sub<MT|vT>;

            if Dimension(LT) lt d then

               V := VectorSpace(K,d);
               B := {V!v:v in Basis(MT)};
               WT := sub<V|B>;
               W := OrthogonalComplement(V,WT);
               L := sub<M|BasisElement(W,1)>;
               return L,3,num;

            end if;

            return M,1,num;

         end if;
      end for;
      
   end while;
   print("Failed to decide before limit.");
   return M,0,num;
end function;


MeatLG:= function(M: NumberMultiplications := 25, limit := 100, Endlimit := 10)
//The Holt-Rees Meataxe with an extension proposed by Charles Leedham-Green.
//This procedure is approximately equivalent to that used by the Magma 
//intrinsic Meataxe.
//We only compute the endomorphism ring after 10 unsuccessful attempts.

   
   K := Field(M);
   d := Dimension(M);
   A := Action(M);

   gen := Generators(A);
   ATgen:={Transpose(a):a in gen};

   num := 0;

   while num le limit or limit eq 0 do
   
      if num eq Endlimit then
         R:=EndomorphismRing(M);
      end if;
      
      num := num+1;
      
      if num gt Endlimit then
      
         fr:=RandomElement(R,NumberMultiplications);
         gr:=RandomElement(R,NumberMultiplications);
         N:=Kernel(fr*gr-gr*fr);
         

         if Dimension(N) lt Dimension(M) and Dimension(N) gt 0 then
         
            L:=sub<M|N>;
            return L,4,num;

         end if;
      end if;

//The below section is the same as Meat(M).

      r := RandomElement(A,NumberMultiplications);
      f := CharacteristicPolynomial(r);
      F := Factorization(f);

      for i in [1..#F] do

         p := F[i][1];
         x := Evaluate(p,r);
         N := NullSpace(x);
         v := BasisElement(N,1);
         L := sub<M|v>;

         if Dimension(L) lt Dimension(M) then
            return L,2,num;
         end if;

         if Dimension(N) eq Degree(p) then

            xT := Transpose(x);
            NT := Nullspace(xT);
            vT := BasisElement(NT,1);
            GT := MatrixGroup<d,K|ATgen>;
            MT := GModule(GT);
            LT := sub<MT|vT>;

            if Dimension(LT) lt d then

               V := VectorSpace(K,d);
               B := {V!v:v in Basis(MT)};
               WT := sub<V|B>;
               W := OrthogonalComplement(V,WT);
               L := sub<M|BasisElement(W,1)>;
               return L,3,num;

            end if;

            return M,1,num;

         end if;
      end for;
      
   end while;
   print("Failed to decide before limit.");
   return M,0,num;
end function;

//The following produces the module described in Ivanyos-Lux section 5.
//This example takes a long time to solve with the Holt-Rees algorithm. 
//ConstructModule(n,p^k) will produce a module over GF(p) of dimension k*n
ConstructModule:=function(n,q) 
   K:=GF(q);
   F:=PrimeField(K);
   L:=MatrixAlgebra(K,n);
   A:=L!SL(n,q).1;
   B:=L!SL(n,q).2;
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
MeatProfile:=function(n,q,m)
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
