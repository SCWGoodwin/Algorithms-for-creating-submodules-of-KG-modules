# Algorithms-for-creating-submodules-of-KG-modules
We have developed Magma implementations of some algorithms for finite dimensional KG-modules based on the following papers:

Meataxe:
Richard A. Parker. The computer calculation of modular characters (the MeatAxe). In Computational group theory (Durham, 1982). pp. 267 - 274 Academic Press, London, 1984.
[HR94] Derek F. Holt and Sarah Rees. Testing modules for irreducibility. J. Austral. Math. Soc. Ser. A, 57(1):1{16, 1994.
[IL00] Gabor Ivanyos and Klaus Lux. Treating the exceptional cases of the MeatAxe. Experiment. Math., 9(3):373{381, 2000.

Submodules:
[LMR94] Klaus Lux, Jurgen Muller, and Michael Ringe. Peakword condensation and submodule lattices: an application of the MEAT-AXE. J. Symbolic Comput., 17(6):529{544, 1994.

Simon Goodwin and Eamonn O'Brien
April 2022
=======================================================

Meataxe.m

=======================================================

Meat(M: NumberMultiplications := 25, limit := 100);

The Holt-Rees Meataxe [HR94].
We use a pseudo-random procedure to generate elements of the action algebra, NumberMultiplications is a parameter of this procedure.
After testing limit number of random elements of A, this will terminate with error message and will return M. To allow any number of attempts, set limit to 0.

Returns M if M is irreducible or the limit was reached, otherwise returns a submodule of M.

Returns a code to indicate how the algoirithm terminated
0 Failed to decide irreduibility before limit
1 M is irreducible
2&3 Found a submodule

Additionally returns number of iterations.


=======================================================

MeatIL:= function(M: NumberMultiplications := 25, limit := 100)

The Holt-Rees Meataxe with the Ivanyos-Lux extension [IL00]
Same options as Meat

Returns M if M is irreducible or the limit was reached, otherwise returns a submodule of M.

Returns a code to indicate how the algoirithm terminated
0 Failed to decide irreduibility before limit
1 M is irreducible
2&3 Found a submodule using Holt-Rees algorithm
4 Found a submodule using the extension.

Additionally returns number of iterations.

=======================================================

MeatLG:= function(M: NumberMultiplications := 25, limit := 100, Endlimit := 10)

The Holt-Rees Meataxe with an extension proposed by Leedham-Green.

The Endomorphism Ring of M will only be calculated after Endlimit attempts to find a submodule of M.
Otherwise, same options as Meat.

Returns M if M is irreducible or the limit was reached, otherwise returns a submodule of M.

Returns a code to indicate how the algoirithm terminated
0 Failed to decide irreduibility before limit
1 M is irreducible
2&3 Found a submodule using Holt-Rees algorithm
4 Found a submodule using the extension.

Additionally returns number of iterations.

=======================================================

ConstructModule(n,q)

Constructs a reducible module of dimension 2en over GF(p) where q = p^e. 
This module will be an example of an "exceptional" module, and the Holt-Rees MeatAxe may take a long time to find a submodule.

=======================================================
=======================================================

lattice.m
