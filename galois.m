Define::usage =
   "Define[u^n, v], where u is a symbol and n is a positive integer,
    defines u to be a root of the polynomial u^n = v.  Define[F[u],v] 
    defines the value of the homomorphism F at u to be v.";

Define[a_Symbol^n_Integer,b_] := Module[{i},
  UsedSymbols = Union[UsedSymbols,{a}];
  a/: a^n := b;
  For[i=n+1, i <= 2n,i++,
     a/: a^i := Evaluate[FixedPoint[Expand,(a^(i-1)) a]]];
  a/: a^m$_ := FixedPoint[Expand,(a^(2n)) (a^(m$-2n))] /; m$ > 2n] /; n > 1 

Define[a_,a_] := Print["Rule already defined."]

Define[F_Symbol[a_],b_] := Module[{},
   F[a] := b;
] /; UnsameQ[ F[a] , b ]

Homomorph::usage =
   "Homomorph[F] defines F to be a homomorphism between two
    fields M and K.";

Homomorph[F_Symbol] := Module[{},
   UsedSymbols = Union[UsedSymbols,{F}];
   ClearAll[Evaluate[F]];
   F[a$_ b$_] := FixedPoint[Expand,F[a$] F[b$]];
   F[a$_ + b$_] := F[a$] + F[b$];
   F[a$_ ^ b$_Integer] := FixedPoint[Expand, F[a$]^b$];
   F[a$_Integer] := a$;
   F[a$_Rational] := a$;];

SetAttributes[Homomorph, HoldAll];

CheckHomo::usage = "CheckHomo[F,D] verifies that F is a homomorphism
   with a domain of D. Note that only a basis of the field D must be given.";

CheckHomo[f_,D_List] := Module[{i,j},
   For[i=Length[D], i>0, i--,
      For[j=Length[D], j>0, j--,
         If[ FixedPoint[Expand, f[D[[i]]]  f[D[[j]]] - f[D[[i]] D[[j]]]] =!= 0,
            Print["f[",D[[i]],"] * f[",D[[j]],
                 "] is not equal to f[", D[[i]],"*", D[[j]],"]"];
            Return[False] ];
         If[ f[D[[i]]] + f[D[[j]]] =!= f[D[[i]] + D[[j]] ],
            Print["f[",D[[i]],"] + f[",D[[j]],
                 "] is not equal to f[", D[[i]] + D[[j]],"]"];
            Return[False] ] ] ];
   Return[True] ]  

ClearDefs::usage = 
   "ClearDefs resets all definitions created by this notebook.";

ClearDefs := Module[{j},
   Unprotect[Plus];
   SetAttributes[Plus,Listable];
   Protect[Plus];
   ClearAll[ZerosList$];
   For[j=1,j<=Length[UsedSymbols],j++,
      ClearAll[Evaluate[UsedSymbols[[j]]]]];
   UsedSymbols = {}; 
]

Group::usage = 
   "Group[X_List] gives a list of elements of the group                
    symbolically presented by the set of generators X and                 
    the inference rules previously defined.";

Group[G_List] := Module[{m, n, i, j, g, Repeat},
   g = Union[G];
   m = Length[g];
   Repeat = True;
   While[Repeat,
      Repeat = False;
      n = Length[g];
      Do[ Do[ If[ MemberQ[g, CenterDot[g[[i]], g[[j]]] ], ,
                  Repeat = True;
                  g = Append[g, CenterDot[g[[i]], g[[j]]] ]
                ], {i,1,n} ], {j,1,m} ] ];
   Sort[g] ]

ToStr[x_] := StringJoin[Select[Characters[ToString[
             If[MemberQ[ToCharacterCode[ToString[x]],10],InputForm[x],x]
             ]],# =!= " " &]]

ColorTable := {RGBColor[1,1,0],RGBColor[1,0,1],RGBColor[0,1,1],
               RGBColor[1,0,0],RGBColor[0,1,0],RGBColor[.6,.4,.8],
               RGBColor[1,.6,0],RGBColor[.7,.8,.7],RGBColor[.8,.6,.5],
               RGBColor[.5,.6,.8],RGBColor[.8,.2,.5],RGBColor[.8,.6,.2],
               RGBColor[.6,.6,.2],RGBColor[1,.4,.4],RGBColor[.2,.8,.7],
               RGBColor[1,.6,1],RGBColor[.7,1,0],RGBColor[0,0,1],
               RGBColor[.6,.4,.4],RGBColor[0,.6,1],RGBColor[1,.8,.7],
               RGBColor[.4,.2,1],RGBColor[1,.8,.4],RGBColor[.2,.6,.4],
               RGBColor[.5,.8,.8],RGBColor[.4,.8,.5],RGBColor[0,1,.6],
               RGBColor[.8,.5,.2],RGBColor[.2,.2,.9]};

SubSetPosition[Q_List,S_] := Module[{i,j},
   If[Head[S] === List,
      j = 0;
      For[i=1,i<=Length[Q],i++,
        If[Complement[S,Q[[i]]] === {}, j = i; i = Length[Q]]],
      If[MemberQ[Q,S],j = Position[Q,S,1][[1]][[1]], j=0]];
   j];

MultTable::usage = 
   "MultTable[X_List] gives a multiplication table of the elements        
    in the list, using different colors for different elements.       
    The list can have no more than 27 elements.";

MultTable[Q_List] := Module[{i,j,T},
   If[Length[Q] > 27, Print["Group too big to print table."],
     T = Table[
      If[i===0,
     If[j===0,RGBColor[1,1,1],ColorTable[[j]]],
      If[j===0,ColorTable[[i]],
       If[MemberQ[Q,CenterDot[Q[[i]],Q[[j]]]],
         ColorTable[[Position[Q,CenterDot[Q[[i]],Q[[j]]],1][[1]][[1]]]],
         RGBColor[0,0,0]]]],{i,Length[Q],0,-1},
                                           {j,0,Length[Q]}];
       If[Max[Table[Length[Characters[ToStr[Q[[i]]]]],
          {i,1,Length[Q]}]]*(Length[Q]+1) < 85,
      Show[Graphics[RasterArray[T]],
          Graphics[Table[
         Text[ToStr[Q[[i]]],{i+.5,Length[Q]+.5}],
                                          {i,1,Length[Q]}]],
         Graphics[Table[
         Text[ToStr[Q[[j]]],{.5,Length[Q] - j + .5}],
                                          {j,1,Length[Q]}]],
         Graphics[Table[
         Text[If[MemberQ[Q,CenterDot[Q[[i]],Q[[j]]]],
                             ToStr[CenterDot[Q[[i]],Q[[j]]]]," "],
           {j + .5, Length[Q] - i + .5}],
            {i,1,Length[Q]},{j,1,Length[Q]}]],
         Graphics[Line[{{1,0},{1,Length[Q]},
                                 {Length[Q]+1,Length[Q]}}]]],
    Show[Graphics[RasterArray[T]],
         Graphics[Table[
    Text[ToStr[Q[[i]]],{-.5,Length[Q] - i + .5},{1,0}],
                                           {i,1,Length[Q]}]],
         Graphics[Line[{{1,0},{1,Length[Q]},
                                  {Length[Q]+1,Length[Q]}}]],
         AspectRatio -> Automatic,
         PlotRange -> All]]]]

ToVector[Q_] := Module[{i,L,X,T},
  X = Expand[Q];
  If[Head[X] =!= Plus, X = {X}];
  L = Length[X];
  T = {};
  For[i=1,i<=L,i++,
    If[NumberQ[X[[i]]],
      If[Head[X[[i]]] === Complex,
        If[Re[X[[i]]] =!= 0,AppendTo[T,{Re[X[[i]]],1}]];
        AppendTo[T,{Im[X[[i]]],I}],
        AppendTo[T,{X[[i]],1}]],
      If[Head[X[[i]]] =!= Times,AppendTo[T,{1,X[[i]]}],
         If[NumberQ[X[[i]][[1]]], 
           AppendTo[T,{X[[i]][[1]],X[[i]]/X[[i]][[1]]}],
           AppendTo[T,{1,X[[i]]}]
           ]
         ]
       ]
      ];
   T]

Vectorize[x_,y_List] := Module[{i,j,Y,M,L,Q,T,Z,Vars},
  Vars = {};
  Y =  Append[y,x];
  M = Length[Y];   
  For[j=1,j<=M,j++,
     Vars = Union[Vars,Transpose[ToVector[Y[[j]]]][[2]]]];
  L = Length[Vars];
  Q = {};
  For[i=1,i<=M,i++,
     T = ToVector[Y[[i]]];
     Z = Table[0,{j,1,L}];
     For[j = 1, j <= Length[T], j++,
        Z[[Position[Vars,T[[j]][[2]]][[1]][[1]]]] = T[[j]][[1]]];
     AppendTo[Q,Z] ];
  Q = RowReduce[Transpose[Q]];
  T = {};
  i=1;
  For[j = 1,j < M,j++,
     If[(i>L)||(Q[[i,j]] === 0),
        AppendTo[T,0],
        AppendTo[T,Q[[i,M]]];
        i++]];
  If[(i>L)||Q[[i,M]] === 0, T , NotInSpan]
]

GeneratorReduce[Basis_List] := Module[{i,j},
  Bas = Union[DeleteCases[Basis,0]];
  M = Length[Bas];   
  Vars = {};
  For[j=1,j<=M,j++,
     Vars = Union[Vars,Transpose[ToVector[Bas[[j]]]][[2]]]];
  L = Length[Vars];
  T = Table[Vectorize[Bas[[j]],Vars],{j,1,M}];
  If[(Flatten[DeleteCases[T, _Integer,2]] === {}) && 
    (Length[Union[Bas,Vars]]===M), Bas = Vars];
  Bas
]

NormFn[Poly_, a_Symbol] := Module[{Pol,i,j,k,n,T,gg,Temp},
   Pol = FixedPoint[Expand,Poly];
   n = 1;
   While[Exponent[a^n,a] === n, n++];
   If[((Variables[a^n] === {a}) || (Variables[a^n] === {}))
            && (Coefficient[Poly /. i_Rational -> j,j]===0),
      QuickNormFn[Poly,a],
      T = {};
      Temp = Sum[ gg[i] a^i,{i,0,n-1}];
      For[i=0,i<n,i++,
         AppendTo[T,Table[Coefficient[FixedPoint[Expand, Temp (a^i)],a,j],{j,0,n-1}]]];
      Temp = Expand[Det[T]];
      For[i=0, i<n, i++,
         Temp = Temp /. gg[i] -> Coefficient[Pol,a,i] ];
      FixedPoint[Expand, Temp]
   ]
]

NormFn[Poly_, {a__Symbol}] := Module[{i,Temp},
   Temp = Poly;
   For[i = Length[{a}], i > 0, i--,
      Temp = NormFn[Temp, {a}[[i]] ]];
   Temp]

QuickNormFn[Poly_,a_Symbol] := Module[{Y,Z,i,n},
   If[Head[ZerosList$[a]] =!= List,
      n = 1;
      While[Exponent[a^n,a] === n, n++];
      Z = NSolve[Y^n == (a^n /. a -> Y), Y, 100];
      If[Length[Z] === n,
          ZerosList$[a] = Table[Z[[i]][[1]][[2]],{i,1,n}],
          Print["The extension variable is not defined properly."]];
   ];
   Z = Expand[Product[Poly /. a -> ZerosList$[a][[i]], 
                            {i,1,Length[ZerosList$[a]]}]];
   Z = Z /. i_Complex -> Round[i];
   Z = Z /. i_Real -> Round[i]
]  

UnNormFn[Poly_, nn_Symbol, X_Symbol, a_Symbol] := Module[
  {Big,B,i,j,k,q,Z,d1,n,m,d,Y,Prod,Temp,T},
  B = {};
  Big = {};
  n = 1;
  While[Exponent[a^n,a] === n, n++];
  If[ Poly[[0]] === Times, Prod = Poly, Prod = {Poly}];
  Prod[[0]] = List;
  m = 1;
  For[k=1,k<=Length[Prod],k++,
     m = Max[m, Exponent[Prod[[k]],X] / n]];
  T = 1;
  If[ m > 1, T = NormFn[X-a,a]];
  For[k=1,k<=m,k++,
     B = {};
     For[ i = 0, i< n, i++,
        Temp = NormFn[(X - nn a)^k + a^i, a];
        AppendTo[B,Table[Coefficient[Coefficient[
                     Temp,nn,k*n-k-j],X,j],{j,0,n-1}]]];
    AppendTo[Big,B];
  ];
  For[k=1,k<=Length[Prod],k++,
    m = Exponent[Prod[[k]],X]/n;
    Prod[[k]] = Prod[[k]]/Coefficient[Prod[[k]],X,m*n];
    Temp = X^m;
    For[i=1,i <= m,i++,
      Z = Coefficient[Prod[[k]] /. X -> X nn,nn,n*m-i];
      If[ i > 1,
          Z = Z - 
          Coefficient[NormFn[Temp /. X ->(nn X - nn a),a],nn,n*m-i]];
      Z = PolynomialQuotient[Z,T^(m-i),X];
      d1 = Table[Coefficient[Z,X,j],{j,0,n-1}];
      d = Transpose[RowReduce[Transpose[Append[Big[[i]],d1]]]][[n+1]];
      Temp = Temp + Sum[d[[j]] a^(j-1)*X^(m-i),{j,1,n}];
    ];
    Prod[[k]] = Temp];
  Prod[[0]] = Times;
Prod]

UnNormFn[Poly_, nn_Symbol, X_Symbol, w_, {a__Symbol}] := Module[
  {Big,B,i,j,k,q,Z,d1,n,m,d,L,Y,Prod,Temp,T,Bas},
  B = {};
  Big = {};
  L = {a};
  Bas = {1};
  For[i=1,i <= Length[L],i++,
     n = 1;
     While[Exponent[L[[i]]^n,L[[i]]] === n, n++];
     Bas = Flatten[Table[ L[[i]]^k Bas[[j]], {k,0,n-1},{j,1, Length[Bas]}]];
   ];
  n = Length[Bas];
  If[ Poly[[0]] === Times, Prod = Poly, Prod = {Poly}];
  Prod[[0]] = List;
  m = 1;
  For[k=1,k<=Length[Prod],k++,
     m = Max[m, Exponent[Prod[[k]],X] / n]];
  T = 1;
  If[ m > 1, T = NormFn[X-w,L]];
  For[k=1,k<=m,k++,
     B = {};
     For[ i = 1, i<= n, i++,
        Temp = NormFn[(X - nn w)^k + Bas[[i]], L];
        AppendTo[B,Table[Coefficient[Coefficient[
                     Temp,nn,k*n-k-j],X,j],{j,0,n-1}]]];
    AppendTo[Big,B];
 ];
  For[k=1,k<=Length[Prod],k++,
    m = Exponent[Prod[[k]],X]/n;
    Prod[[k]] = Prod[[k]]/Coefficient[Prod[[k]],X,m*n];
    Temp = X^m;
    For[i=1,i <= m,i++,
      Z = Coefficient[Prod[[k]] /. X -> X nn,nn,n*m-i];
      If[ i > 1,
          Z = Z - 
          Coefficient[NormFn[Temp /. X ->(nn X - nn w),L],nn,n*m-i]];
      Z = PolynomialQuotient[Z,T^(m-i),X];
      d1 = Table[Coefficient[Z,X,j],{j,0,n-1}];
      d = Transpose[RowReduce[Transpose[Append[Big[[i]],d1]]]][[n+1]];
      Temp = Temp + Sum[d[[j]] Bas[[j]]*X^(m-i),{j,1,n}];
    ];
    Prod[[k]] = Temp];
  Prod[[0]] = Times;
Prod]

SimpleExtension[a__Symbol] := Module[{L,i,j,k,n,w,p,Bas,d,pp,M},
   L = {a};
   Bas = {1};
   w = Sum[L[[i]],{i,1,Length[L]}];
   p = 1;
   d = 1;
   For[i=1,i <= Length[L],i++,
      n = 1;
      While[Exponent[L[[i]]^n,L[[i]]] === n, n++];
      Bas = Flatten[Table[ L[[i]]^k Bas[[j]], {k,0,n-1},{j,1, Length[Bas]}]];
   ];
   n = Length[Bas];
   While[
     M= {Vectorize[1,Bas]};
     pp = 1;
     For[i = 1, i<= n - 1, i++,
        pp =FixedPoint[Expand,w pp];
        AppendTo[M,Vectorize[pp,Bas]]];
     RowReduce[M][[n]][[n]] == 0,
     w = w + d L[[p]];
     p++;
     If[d < Length[L], d++];
     If[p > Length[L], p = 1];
   ];
w]

FactorLister[Poly_] := Module[{Temp, L, i, j, k },
   Temp = FactorList[Poly];
   If[Temp === {}, Temp = {{1,1}}];
   If[NumberQ[Temp[[1]][[1]]] && (Length[Temp] > 1),
      L = {Expand[Temp[[1]][[1]] Temp[[2]][[1]]]}; k = 2,
      L = {Temp[[1]][[1]]}; k = 1
   ];
   For[i=1, i < Temp[[k]][[2]],i++,
      L = {L, Temp[[k]][[1]]}];
   For[i=k+1, i <= Length[Temp], i++,
      For[j=0, j < Temp[[i]][[2]], j++,
         L = {L, Temp[[i]][[1]]}]];
   Flatten[L]
]


QuickFactor[Poly_, X_Symbol, {a__Symbol}] :=
   Module[{Temp, L, b, i},
   L = {a};
   b = Last[L];
   L = Drop[L, -1];
   Temp = Poly /. X -> X - (2^Length[L] + 1) b;
   Temp = NormFn[Temp, b];
   If[Length[L] > 0,
      QuickFactor[Temp, X, L],
      (Length[FactorLister[Temp]] > 1)]
]

TotalFactor[Poly_, X_Symbol, {a__Symbol}] :=
   Module[{nn, Temp, L, b, i, Prod},
   Prod = FactorLister[Poly];
   For[i=1,i<=Length[Prod], i++,
      If[(Length[CoefficientList[Prod[[i]],X]] > 2) &&
                             QuickFactor[Prod[[i]],X,{a}], 
        If[Length[{a}] > 1, w = SimpleExtension[a],w = a];
        Temp = Prod[[i]];
        For[j =Length[{a}], j > 0, j--,
           Temp = Temp /. X -> X - nn Coefficient[w,{a}[[j]],1] {a}[[j]];
           Temp = NormFn[Temp, {a}[[j]]]];
        Temp = Factor[Temp];
        If[Temp[[0]] === Times,
           Prod[[i]] = UnNormFn[Temp, nn, X, w, {a}]];
       ]
   ];
   Prod[[0]] = Times;
   Prod
]

Unprotect[P, OrderedQ, Sort, Factor];
ClearAttributes[Factor, Listable];

P::usage = "P[i, j, k, ...] denotes the permutation that sends 1 to i,
            2 to j, 3 to k, etc.";

P/: CenterDot[P[x___Integer], P[y___Integer]] := 
   Module[{ u, L, M, Temp, i},
      L = {x};
      M = {y};
      u = Max[Length[L], Length[M]];
      For[ i = Length[L] + 1, i <= u, i++, AppendTo[L,i] ];
      For[ i = Length[M] + 1, i <= u, i++, AppendTo[M,i] ];
      Temp = L;
      For[ i = 1, i <= u, i++, Temp[[i]] = L[[M[[i]] ]] ];
      While[ Temp[[u]] == u, Temp = Delete[Temp,u]; u--];
      Temp[[0]] = P;
      Temp
   ]

P[a___Integer, b_Integer] := P[a] /; Length[{a}] === b-1;

OrderedQ[{P[a___Integer],P[b___Integer]}] := Module[{i},
   If[Length[P[a]] > Length[P[b]], Return[False] ];
   If[Length[P[a]] < Length[P[b]], Return[True] ];
   For[i=Length[P[a]], i>0, i--,
      If[P[a][[i]] < P[b][[i]], Return[False] ];
      If[P[a][[i]] > P[b][[i]], Return[True] ] ];
   Return[True] ]

Sort[a_] := Sort[a, OrderedQ[{#1, #2}]&]

P[a___Integer][b_] := If[ b>0 && b <= Length[{a}],
    P[a][[b]],b,b]

AnOrSn[Polynom_,Quad_,L_,H_] := Module[{X,i,j,k,R,T,d,dd,n,d0,d1,Bas,M,Temp},
   X = Variables[Polynom][[1]];
   R = NSolve[Polynom==0,X,20];
   R = Table[R[[i]][[1]][[2]],{i,Length[R]}];
   k = Product[R[[i]]-R[[j]],{i,1,Length[R]-1},{j,i+1,Length[R]}];
   k = Sqrt[Round[k^2]];
   If[IntegerQ[k],  
     T = Table[X - H[[i]],{i,1,Length[H]}];
     dd = Expand[X^2 - Quad/Coefficient[Quad,X,2]] /. X -> d;
     Define[d^2,dd];
     AppendTo[T,d];
     AppendTo[T,X - (PolynomialQuotient[Quad,X-d,X]/ Coefficient[Quad,X,2])];
     R = Product[T[[i]]-T[[j]],{i,1,Length[T]-1},{j,i+1,Length[T]}] - k;
     R = FixedPoint[Expand,R];
     d1 = Coefficient[R,d,1];
     d0 = Coefficient[R,d,0];
     Bas = {1};
     For[i=1,i <= Length[L],i++,
        n = 1;
        While[Exponent[L[[i]]^n,L[[i]]] === n, n++];
        Bas = Flatten[Table[ L[[i]]^k Bas[[j]], {k,0,n-1},{j,1, Length[Bas]}]];
      ];
     n = Length[Bas];
     M = {Table[If[IntegerQ[Bas[[i]]], j = Select[d1, IntegerQ],
          j = Coefficient[d1,Bas[[i]]];
          If[IntegerQ[j],,
              If[j[[0]]=== Plus,j = Select[j,IntegerQ],j=0]]];
          j,{i,1,n}]};
     For[k=2, k<=n,k++,
         R = FixedPoint[Expand, d1 Bas[[k]]];
         AppendTo[M, Table[If[IntegerQ[Bas[[i]]], j = Select[R, IntegerQ],
          j = Coefficient[R,Bas[[i]]];
          If[IntegerQ[j],,
              If[j[[0]]=== Plus,j = Select[j,IntegerQ],j=0]]];
          j,{i,1,n}]]];
     AppendTo[M, Table[If[IntegerQ[Bas[[i]]], j = Select[-d0, IntegerQ],
          j = Coefficient[-d0,Bas[[i]]];
          If[IntegerQ[j],,
              If[j[[0]]=== Plus,j = Select[j,IntegerQ],j=0]]];
          j,{i,1,n}]];
     M = Transpose[RowReduce[Transpose[M]]][[n+1]];
     Temp = X - Sum[M[[i]] Bas[[i]],{i,1,n}];
     Temp = Temp*PolynomialQuotient[Quad,Temp,X],
     Temp = Quad];
   Temp]

Factor[Polynom_,a__Symbol] := Module[{X, Temp, i,j,k,n,L,T,U,Poly},
   X = Variables[Polynom];
   L = {a};
   T = L;
   For[i=1,i<=Length[L],i++,
     n = 1;
     While[Exponent[L[[i]]^n,L[[i]]] === n, n++];
     T = Union[L, Variables[L[[i]]^n]]
   ];
   X = Complement[X, T];
   If[Length[X] > 1, 
      Print["Only one variable in the polynomial can be indeterminate."],
      X = X[[1]];
      Poly = FactorList[Polynom];
      k = Length[Poly];
      T = 1;
      For[j=1,j<=k,j++,
         Temp = Poly[[j]][[1]];
         For[i=1,i<= Length[L],i++,
            If[FixedPoint[Expand, Temp /. X -> L[[i]] ] === 0,
               T = T*(X - L[[i]])^Poly[[j]][[2]]; 
               Temp = PolynomialQuotient[Temp, X - L[[i]], X];
               U = X - PolynomialQuotient[
                       X^2 - L[[i]]^2 /. L[[i]] -> X,X-L[[i]],X];
               If[FixedPoint[Expand, Temp /. X -> U ] === 0, 
                 T = T*(X - U)^Poly[[j]][[2]]; 
                 Temp = PolynomialQuotient[Temp, X - U, X] ];
               i--] ];
         If[(T[[0]] === Times) && 
            (Length[T] + 2 === Exponent[Polynom,X]) &&
            (Length[Variables[Polynom]] === 1) &&
            (Exponent[Temp,X] === 2),
             Temp2 = AnOrSn[Polynom,Expand[Temp],L,T];
             If[(Temp2 === Temp)&&(Length[L] + 2 < Exponent[Polynom,X]),
                Temp2 = TotalFactor[Temp, X, L]];
             T = T*Temp2,
         T = T*TotalFactor[Temp, X, L]^Poly[[j]][[2]]];
      ];
      T
   ]   
]

Protect[P, OrderedQ, Sort, Factor];  

