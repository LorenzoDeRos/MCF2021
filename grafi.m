____________________________GENERAGRAFI____________________________________________

grafobase = {{1, -1}, {2, -1}, {3, -1}};
generagrafi[n_]:=Module[{temp},
	i=3;
	listagrafi={grafobase};
	While[
		i<=n,
		(*Flatten toglie un livello, da lista di lista di grafi a lista di grafi*)
		nuovigrafi3=Flatten[Map[inserzione3, listagrafi],1];
		nuovigrafi4=Flatten[Map[inserzione4, listagrafi],1];
		listagrafi=Join[nuovigrafi3,nuovigrafi4];
		++i;
	];
	listagrafi
];

(*inserisco un vertice in ogni linea*)
(*Length[grafo] \[EGrave] il numero di linee nel grafo*)

inserzione3[grafo_]:=Module[{temp},
	indici=Flatten[grafo];
	npt=Max[indici];
	nvert=Min[indici];
	nuovigrafi=Table[
		inserisci3[i,npt+1,nvert-1,grafo],
		{i,1,Length[grafo]}
		];
	nuovigrafi
];

(*come si inserisce una linea in un grafo*)
(*pos \[EAcute] la posizione della linea su cui voglio fare la inserzione*)
(*ext \[EGrave] il punto esterno da aggiungere*)

inserisci3[pos_,ext_,int_,grafo_]:=ReplacePart[
	(*oggetto da modificare*)
	grafo,
	(*pippo \[EGrave] il nuovo elemento che voglio sostituire*)
	pippo[
		{ext,int},
		{grafo[[pos,1]],int},
		{grafo[[pos,2]],int}
		],
	pos
	] /. pippo->Sequence;

inserzione4[grafo_]:=Module[{temp},
	indici=Flatten[grafo];
	npt=Max[indici];
	nvert=Min[indici];
	nuovigrafi=Table[
		inserisci4[i,npt+1,grafo],
		{i,-1,nvert,-1}
	];
	(*cancello tutte le volte in cui inserisci 4 non ha potuto fare nulla*)
	(*perch\[EAcute] il vertice su cui ha agito era saturo di linee*)
	nuovigrafi=DeleteCases[nuovigrafi,{}];
	nuovigrafi
];

inserisci4[vertice_, ext_, grafo_]:=If[
	(*controllo che il vertice abbia tre linee attaccate*)
	(*cio\[EAcute] quante volte compare il vertice al secondo livello nella lista*)
	Count[grafo,vertice,2]===3,
	Append[grafo, {ext,vertice}],
	(*se un vertice ha gi\[AGrave] quattro linee aggiungo una linea vuota*)
	{}
];

____________________________GENERAEQUAZIONI_________________________________________

listacaratteristiche[grafo_, F_]:=Map[(Apply[F,#])&, grafo];

generaequazioni[grafo_, F_]:=Module[{temp, caratteristiche},
	indici=Flatten[grafo];
	npt=Max[indici];
	nvert=Min[indici];
	caratteristiche=listacaratteristiche[grafo, F];
	equazioni=Table[
		(*di default il pattern viene cercato da Cases al I livello*)
		carattvertice=Join[Cases[caratteristiche,F[_,i]],-Cases[caratteristiche,F[i,_]]];
		eq = Apply[Plus,carattvertice]==0;
		eq,
		{i,-1,nvert,-1}
	];
	equazioni=equazioni /. {F[i_ /; i>0, j_] :> F[i]};
	incognite=Cases[
		equazioni,
		F[_,_],
		(*il prossimo argomento serve a dire che il pattern*)
		(*va cercato a qualunque livello della espressione*)
		Infinity
	];
	globale=Rule[F[npt],-Sum[F[k],{k,1,npt-1}]];
	equazioni=equazioni /. globale;
	impulsiinterni=Solve[equazioni, incognite];
	impulsiinterni
];

____________________________VERTICIPROPAGATORI_____________________________________

verticipropagatori[grafo_, F_]:=Module[{temp,indici,nvert,vertici,propagatori},
    indici=Flatten[grafo];
    nvert=Min[indici];
    vertici=Table[
        Which[
            Count[grafo, {___,i,___}]===3,
            V3[i] @@ Cases[listacaratteristiche[grafo, F], F[___,i,___]],
            Count[grafo, {___,i,___}]===4,
            V4[i] @@ Cases[listacaratteristiche[grafo, F], F[___,i,___]]
        ],
        {i,-1,nvert,-1}
    ];
    vertici=vertici /. {F[i_ /; i > 0, j_] :> F[i]};
	vertici=Flatten[vertici /. generaequazioni[grafo, F],1];
    propagatori=Map[Prop,Cases[grafo,{i_ /; i<0, j_ /; j<0}]];
    propagatori=propagatori /. Prop[{a_,b_}]->Prop[a,b];
    Return[Times @@ Join[vertici,propagatori]];
];
