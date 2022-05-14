// This function takes a peakword and (nearly, see Warning page 8 of LMR) 
// produces the condensed module with respect to that peakword. 
// The matrix N is the uncondensation function from U to M.

PeakWordCondense := function(pkwd, M, A)
   G:=ActionGroup(M);
   n := Dimension(M);
   F := BaseRing(M);
   V := VectorSpace(M);
   N := 1;
   K := Kernel(pkwd);
   while N lt Dimension(M) do
      d := Dimension(K);
      N +:= 1;
      peak := pkwd^N;
      K := Kernel(peak);
      if d eq Dimension(K) then break; end if;
   end while;
   I := Image(peak);
   // K := Kernel(pkwd^N);
   Q, p := V/I;
   pi := Matrix([p(V.i):i in [1 .. n]]);
   m1 := BasisMatrix(K);
   N := (m1*pi)^-1*m1;
   gens := [Generic (A) | A.i: i in [1..Ngens(A)]];
   for i in [1..10] do
      Append(~gens, Random(G:Short:=true));
   end for;
   eAe := sub<MatrixAlgebra(F, Dimension(K)) | [N*a*pi: a in gens]>;
   U := RModule(eAe);
   return U, N;
end function;

RandomCondensations := function(M, A, C)
   Condensations := [[]:i in [1..#C]];
   CondensationMatrices := [* [* *]: i in [1..#C]*];
   for j in [1..10] do
      _, pkwds := Peakwords(C: M1 := M);
      for i in [1..#pkwds] do
         U, N := PeakWordCondense(pkwds[i], M, A);
         Append(~Condensations[i], U);
         Append(~CondensationMatrices[i], N);
      end for;
   end for;
   MinConds := [];
   MinCondMatrices := [* *];
   for i in [1..#pkwds] do
      _, minpos := Min([Dimension(U): U in Condensations[i]]);
      Append(~MinConds, Condensations[i][minpos]);
      Append(~MinCondMatrices, CondensationMatrices[i][minpos]);
   end for;
   return MinConds, MinCondMatrices;
end function;

// Compute all cyclic submodules of a given module.
// Each vector is spun up and a list of distinct 
// submodules and their generators is stored.
CyclicSubmodules := function(U)

   CyclicGens := [];
   Cyclics := {@ @};

   for v in U do
      vd:=Depth(v);
      if vd ne 0 then
         if v[Depth(v)] eq 1 then
            W := sub<U | v>;
            if not W in Cyclics then
               Include(~Cyclics, W);
               Append(~CyclicGens, v);
            end if;
         end if;
      end if;
   end for;
   return CyclicGens, Cyclics;
end function;

AltCyclicSubmodules:=function(U)

   C := Constituents(U);
   
   d := Dimension(C[1]);
   L := SubmoduleLattice(U);
   Cyclics := {@Module(x):x in L|Dimension(x)-Dimension(JacobsonRadical(x)) eq d@};
   CyclicGens := [];
   for V in Cyclics do
      dimV := Dimension(V);
      for i in [1..dimV] do
         if Dimension(sub<V|V.i>) eq dimV then
            Append(~CyclicGens,U!V.i);
            break;
         end if;
      end for;
   end for;

return CyclicGens,Cyclics;

end function;

// For a sequence of submodules L, return a #L by #L matrix Inc
// where Inc[j, i] = 1 if L[i] subset L[j], and 0 otherwise.
// So the j-th row contains 1s for the modules contained in module L[j]. 

IncidenceMat := function(L)
   Inc:=ZeroMatrix(IntegerRing(),#L,#L);
   for i in [1..#L] do
      for j in [1..#L] do
         if L[i] subset L[j] then
            Inc[j, i] := 1;
         end if;
      end for;
   end for;
   return Inc;
end function;

// Given a list of cyclic submodules L, we produce a matrix B
// where B[i, j] = 0 if L[i] subset L[j] or L[j] subset L[i]
// and otherwise B[i, j] is a positive integer such that
// B[i, j] = B[k, l] if and only if L[i]+L[j] = L[k]+L[l].

BiCyclicMatrix := function(L)
   B := ZeroMatrix(IntegerRing(), 0, 0);
   NBC := 0;
   for ind in [1..#L] do
      Cyclics := L[ind];
      m := #Cyclics;
      BiCyclics := {@ @};
      BiCyMat := ZeroMatrix(IntegerRing(), #Cyclics, #Cyclics);
      for i in [1..#Cyclics] do
         W1 := Cyclics[i];
         for j in [i+1..#Cyclics] do
            W2 := Cyclics[j];
            Z := W1+W2;
            if Dimension(Z) eq Maximum(Dimension(W1), Dimension(W2)) then
               continue j;
            end if;
            IBi := Index(BiCyclics, Z);
            if IBi eq 0 then
               Include(~BiCyclics, Z);
               IBi := #BiCyclics;
            end if;
            BiCyMat[i,j] := IBi+NBC;
            BiCyMat[j,i] := IBi+NBC;
         end for;
      end for;
      B := DiagonalJoin(B, BiCyMat);
      NBC := Max({B[i,j]:i in [1..Nrows(B)], j in [1..Nrows(B)]});
   end for;
   return B, NBC;
end function;

// Find a dotted line for each bicyclic module.

DottedLines := function(B, NBC)
   DL := [];
   for i in [1..NBC] do
      S := {@ {j,k} : j in [1..Nrows(B)], k in [1..Nrows(B)] | B[j,k] eq i @};
      Gr := Graph<Nrows(B) | S>;
      _,clique:=HasClique(Gr,2,true,1);
      DL := DL cat [{Index(v):v in x}: x in {clique} | #x ge 3];
   end for;
   return DL;
end function;

// Compute the lattice of complete sets, which is isomorphic
// (as lattices) to the submodule lattice

CompleteSets := function(Inc, DL)
   print "Calculating Submodules";
   NL := Nrows(Inc);
   Cycs := {@ {j: j in [1..NL] | Eltseq(Inc[i])[j] eq 1}: i in [1..NL] @};
   Subs := {x: x in Cycs};
   NewSubs := Subs;
   DLinesByn := [{D: D in DL | i in D}: i in [1..NL]];
   Checked := {x: x in Cycs};
   
   cont := true;
   while cont do
   printf "Current Number of Submodules: %o\n", #Subs;
   for x in Cycs do
      Y := {x join x2: x2 in Subs};
      Z := Y diff Checked;
      Checked join:= Y;
      
      for y in Z do
         z := y;
         Newz := z;
         comp := true;
         while comp do
            zDL := &join [DLinesByn[i]: i in Newz];
            Oldz := z;
            comp := false;
            
            zDLS:=[D:D in zDL];
            DzS:=[D diff z:D in zDLS];
            DzFS:=[D:i->D in DzS|#D le #zDLS[i]-2];
            AddCyclics:=&join DzFS;
            AddNums:=&join {Cycs[m]:m in AddCyclics};
            if AddNums ne {} then
               z:=z join AddNums;
               comp:=true;
            end if;
            Newz := z diff Oldz;
            
            for D in zDL do
               Dz := D diff z;
               if #Dz le #D-2 then
                  for m in Dz do
                     comp := true;
                     z := z join Cycs[m];
                  end for;
               end if;
            end for;
            Newz := z diff Oldz;
         end while;

         if not z in Subs then
            Include(~Subs, z);
         end if;
      end for;
      end for;
      
   end while;
   return Subs;
end function;

BitCompleteSets := function(Inc, DL)
   NL := Nrows(Inc);

   cont := true;
   print "Calculating Submodules";
   
   Cycs := {@Seqint(Eltseq(Inc[i]), 2):i in [1..NL]@};
   Subs := {x: x in Cycs};
   
   DLB := [[0: i in [1..NL]]: D in DL];
   
   for j in [1..#DLB] do
      for i in [1..NL] do
         if i in DL[j] then
            DLB[j][i] := 1;
         end if;
      end for;
   end for;
   
   DLBits := {Seqint(D, 2): D in DLB};
   
   Checked := {x:x in Cycs};
   nump:=0;
   while cont do
   for x in Cycs do
      Y := {BitwiseOr(x, x2):x2 in Subs};
      n := #Subs;
      Z := Y diff Checked;
      Checked join:= Y;
      //printf "Current Number of Submodules: %o\n", #Subs;
      //printf "Completing %o Sets\n", #Z;
      nump+:=#Z;
      
      for y in Z do
         
         z := y;
         comp := true;
         while comp do
            zOld := z;
            for D in DLBits do
               zD := BitwiseAnd(D, z);
               if BitwiseAnd(zD, zD-1) ne 0 then
                  z := BitwiseOr(z, D);
               end if;
            end for;
            if zOld eq z then
               comp := false;
            end if;
         end while;
         if not z in Subs then
            Include(~Subs, z);
         end if;
      end for;
   end for;
      
      if n eq #Subs then cont := false; end if;
   end while;
   
   SeqSubs := [Intseq(S, 2):S in Subs];
   SeqSubs := [S cat [0:i in [1..NL-#S]]:S in SeqSubs];
   SetSubs := [{i:i in {1..NL}|S[i] eq 1}: S in SeqSubs];
   return SetSubs;
   
end function;

// Main function 

function MySubmodules(M: ReturnMods := false, Bit := true, LatticeCyclics:=false)


   A := Action(M);
   C := Constituents(M);
   l := #C;
   //Return {M, 0} if M is simple.
   if IsIrreducible(M) then
      return {M, sub<M | 0>};
   end if;
   
   print "Condensing";
   LocalSubList := [* *];
   CyclicSubList := [* *];
   LocalSubs := [];
   CondMods, CondMatrices := RandomCondensations(M, A, C);
   printf "Condensed Module Dimensions: %o\n", [Dimension(U): U in CondMods];
   
   for i in [1..l] do
      Locals := [];
      U := CondMods[i];
      N := CondMatrices[i];
      VS := VectorSpace(U);
      
      // We must find all cyclic submodules of each condensed module
      print "Calculating cyclics";
      if LatticeCyclics then
         CyclicGens, Cyclics := AltCyclicSubmodules(U);
      else 
         CyclicGens, Cyclics := CyclicSubmodules(U);
      end if;
      UCyclicGens := [VS!v*N: v in CyclicGens];
      
      // If the condensed algebra is not equal to eAe, we may need to
      // combine some cyclic submodules which uncondense to the same module.
      
      tocombine := [];
      for i -> v in UCyclicGens do
         W := sub<M | v>;
         ILocals := Index(Locals, W);
         if ILocals ne 0 then
            Exclude(~UCyclicGens, v);
            Append(~tocombine[ILocals], Cyclics[i]);
         else
            Append(~tocombine, [Cyclics[i]]);
            Append(~Locals, W);
         end if;
      end for;
      
      NewCyclics := [&+tocombine[i]: i in [1..#tocombine]];
      LocalSubs cat:= Locals;
      Append(~LocalSubList, Locals);
      Append(~CyclicSubList, NewCyclics);
   end for;
   
   print "Calculating Dotted Lines";
   NL := #LocalSubs;
   Inc := IncidenceMat(LocalSubs);
   B, NBC := BiCyclicMatrix(CyclicSubList);
   DL := DottedLines(B, NBC);
   
   Subs := Bit eq true select BitCompleteSets(Inc, DL) else CompleteSets(Inc, DL);
   
   
   if ReturnMods then
      SubM := {};
      for S in Subs do
         Include(~SubM, &+[LocalSubs[j]:j in S]);
      end for;
      Include(~SubM, sub<M | 0>);
      return SubM, LocalSubs;
   end if;
   
   Append(~Subs,{});
   
   return Subs, LocalSubs;
end function;

// Example, Permutation module for the edge group of the Cube graph
// Cube := KCubeGraph(4);
// G := EdgeGroup(Cube);
// M := PermutationModule(G, GF(2));
