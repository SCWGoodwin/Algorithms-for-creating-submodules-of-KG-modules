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
            gens[s] := gens[s] * gens[t];
         elif u eq 2 then 
            gens[s] := gens[t] * gens[s];
         elif u eq 3 then 
            gens[s] := gens[s] + gens[t];
         end if;
      end if;
      v := Random ([1,2]);
      if v eq 1 then 
         gens[NmrGens] *:= gens[s];
      else
         gens[NmrGens] +:= gens[s];
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
   K := Field(M);
   d := Dimension(M);
   A := Action(M);

   gen := Generators(A);
   ATgen:={Transpose(a):a in gen};

   num := 1;
   while num le limit do

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
            return L,1,num;
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
               return L,2,num;

            end if;

            return M,3,num;

         end if;
      end for;
      num := num+1;
   end while;
   print("Failed to decide before limit.");
   return M;
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

   num := 1;

   while num le limit do

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
            return L,1,num;
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
               return L,2,num;

            end if;

            return M,3,num;

         end if;
      end for;
      num := num+1;
   end while;
   print("Failed to decide before limit.");
   return M;
end function;


MeatLG:= function(M: NumberMultiplications := 25, limit := 100)

   R:=EndomorphismRing(M);
   K := Field(M);
   d := Dimension(M);
   A := Action(M);

   gen := Generators(A);
   ATgen:={Transpose(a):a in gen};

   num := 1;

   while true do

      fr:=RandomElement(R,NumberMultiplications);
      gr:=RandomElement(R,NumberMultiplications);
      N:=Kernel(fr*gr-gr*fr);

      if Dimension(N) lt Dimension(M) and Dimension(N) gt 0 then

         return N,3,false;

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
            return L,1,num;
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
               return L,2,num;

            end if;

            return M,3,num;

         end if;
      end for;
      num := num+1;
   end while;
   print("Failed to decide before limit.");
   return M;
end function;
