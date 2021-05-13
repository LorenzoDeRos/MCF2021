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

listaimpulsi[grafo_]:=Map[(Apply[p,#])&, grafo];

conservazioneimpulsi[grafo_]:=Module[{temp, impulsi, impulsivertice},
	indici=Flatten[grafo];
	npt=Max[indici];
	nvert=Min[indici];
	impulsi=listaimpulsi[grafo];
	equazioni=Table[
		(*di default il pattern viene cercato da Cases al I livello*)
		impulsivertice=Join[Cases[impulsi,p[_,i]],-Cases[impulsi,p[i,_]]];
		eq = Apply[Plus,impulsivertice]==0;
		eq,
		{i,-1,nvert,-1}
	];
	equazioni=equazioni /. {p[i_ /; i>0, j_] :> p[i]};
	incognite=Cases[
		equazioni,
		p[_,_],
		(*il prossimo argomento serve a dire che il pattern*)
		(*va cercato a qualunque livello della espressione*)
		Infinity
	];
	globale=p[npt]->-Sum[p[k], {k,1,npt-1}];
	equazioni=equazioni /. globale;
	result=Solve[equazioni, incognite];
	result
];

____________________________VERTICIPROPAGATORI_____________________________________

verticipropagatori[grafo_]:=Module[{temp,indici,nvert,vertici,propagatori},
    indici=Flatten[grafo];
    nvert=Min[indici];
    vertici=Table[
		vertconnessi=Flatten[Cases[grafo, {___,i,___}],1];
		vertconnessi=DeleteCases[vertconnessi, i];
        Which[
            Length[vertconnessi]===3,
            V3[i][vertconnessi],
            Length[vertconnessi]===4,
            V4[i][vertconnessi]
        ],
        {i,-1,nvert,-1}
    ];
    propagatori=Map[Prop,Cases[grafo,{i_ /; i<0, j_ /; j<0}]];
    propagatori=propagatori /. Prop[{a_,b_}]->Prop[a,b];
    Return[Times @@ Join[vertici,propagatori]];
];

_________________________CARATTERISTICHEVERTICI______________________________________

(*aggiungicaratteristiche[vp_]:=Module[{temp},
	newvp = vp /. V3[j_][{a_,b_,c_}] -> V3[j][{p[j,a],p[j,b],p[j,c]},{mu[a],mu[b],mu[c]}];
	newvp = newvp /. V4[j_][{a_,b_,c_,d_}] -> V4[j][{p[j,a],p[j,b],p[j,c],p[j,d]},{mu[a],mu[b],mu[c],mu[d]}];
	newvp = newvp /. p[j_,a_] /; j>a -> -p[j,a];
	newvp = newvp /. p[j_,a_] /; j<a -> p[a,j];
	newvp = newvp /. Prop[j_,k_] -> Prop[j,k][p[j,k],{mu[j],mu[k]}];
	newvp = newvp /. p[j_,k_] /; j>0 -> p[j];
	newvp = newvp /. p[j_,k_] /; k>0 -> p[k];
	Return[newvp];
];*)

aggiungicaratteristiche[vp_,caratt_List]:=Module[{temp},
	newvp = vp /. V3[i_Integer][l_List] :> V3[
							Table[
								If[
									caratt[[k]]===p,
									Map[caratt[[k]][i,#] &, l],
									Map[caratt[[k]],l]
								],
								{k,1,Length[caratt]}
							]
						];
	newvp = newvp /. V4[i_Integer][l_List] :> V4[
							Table[
								If[
									caratt[[k]]===p,
									Map[caratt[[k]][i,#] &, l],
									Map[caratt[[k]],l]
								],
								{k,1,Length[caratt]}
							]
						   ];
	newvp = newvp /. p[j_,a_] /; j>a -> -p[j,a];
	newvp = newvp /. p[j_,a_] /; j<a -> p[a,j];
	newvp = newvp /. Prop[i_Integer,j_Integer] :> Prop[
								Sequence @@ Table[
										If[
											caratt[[k]]===p,
											p[i,j],
											Map[caratt[[k]],{i,j}]
										],
										{k,1,Length[caratt]}
								]
							];
	newvp = newvp /. {p[i_ /; i>0, j_] :> p[i]};
	Return[newvp];
];
