(* ::Package:: *)

(* ::Section:: *)
(*Functional Causal Model*)


(* ::Text:: *)
(*A functional causal model is a Graph of nodes decorated with literal, Hold, or Function-valued Properties. For example fcm = Graph[vs, es] with components:*)
(*    \[FilledSmallCircle] vs = {Property[x, value->42], Property[y, value->Function[{a,b},a+b]],Property[w,value->3]}*)
(*    \[FilledSmallCircle] es = {w->y,x->y}*)
(*Each variable v occurs on the left side of Property exactly once. The interpretation of the fcm is that v takes its value from the respective value property of the right hand side . When the value is a Function, its arguments are the parent values of the parent vertices of the edges es into v given by the Graph.*)
(**)
(*QUICK*)
(*Graph[{v1,v2,v3},{v1->v2,v2->v3,v1->v3}];*)
(*g=setPropertyList[%,value,{v1->Hold[Random[]],v2->(#1 42&),v3->(#1+#2+10&)}];*)
(*Table[evalCausalGraph[g2], {5}]//TableForm*)
(**)
(*EXAMPLE 1*)
(*g=Graph[{xv,yv,zv, ev},{xv->yv,zv->yv,ev->yv}]*)
(*g1=setPropertyList[g,value,{xv->42,ev->Hold[RandomVariate[NormalDistribution[0,1]]],zv->Hold[RandomVariate@ExponentialDistribution[1]],yv->(#1+#2+#3&)}];*)
(*g2=setPropertyList[g,value,{xv->42,ev->Hold[RandomVariate[NormalDistribution[0,1]]],zv->0,yv->(#1+#2+#3&)}]*)
(*bins={40,44,0.1}*)
(*Histogram[#]&@Table[evalCausalGraph[g1], {15000}][[All,3]]*)
(*Histogram[#]&@Table[evalCausalGraph[g2], {15000}][[All,3]]*)
(**)
(*EXAMPLE 2 - Pearl Chapter 6.2.2: Causality without Association*)
(*ClearAll[g,g1]*)
(*g=Graph[{z1v, z2v, xv, yv} ,{z1v->xv,z2v->xv,z1v->yv,z2v->yv}];*)
(*g1=setPropertyList[g,value,{z1v->Hold[RandomInteger[1]],z2v->Hold[RandomInteger[1]],xv->(BitXor[#1,#2]&),yv->(BitAnd[#1,#2]&)}];*)
(*Table[evalCausalGraph[g1],{100}]*)
(**)
(*DETAILS*)
(*There are three supported ways to declare the Graph g:*)
(*    \[FilledSmallCircle] as above and with separate Properties*)
(*    \[FilledSmallCircle] Graph[vs, es, Properties->{x->{value->42},y->{value->Function[..]},w->{value->3}}}]*)
(*    \[FilledSmallCircle] gp = setPropertyList[g, value, {x->42, y->Hold@Random[], z->(#1+#2&)}]*)


(* ::Input::Initialization:: *)
ClearAll[vertexParents]
vertexParents[es_,v_]:=(*
	Returns the distinct parents of e within edges es *)
	Module[{ps},
	ps=First/@Cases[es,_\[DirectedEdge]v];
	If[ps=={},{v},ps]]

ClearAll[vertexListParents]
vertexListParents[es_,vl_]:=(*
	Returns the distinct parents of vl within edges es *)
	Union@@(vertexParents[es,#]&/@vl)

ClearAll[graphRoots]
graphRoots[g_]:=(*
	Returns the parentless vertices of g (ie roots) *)
	If[AcyclicGraphQ@g,FixedPoint[vertexListParents[EdgeList@g,#]&,VertexList@g]]

ClearAll[bfsScan]
bfsScan[g_]:=(*
	Scan over vertices of g in breadth first order *)
	Module[{vs,rs,es1,es2,esp,s0,bfsVisit},
		vs={};
		bfsVisit[v_]:=(
		vs=Prepend[vs,v];
		Print[vs]);
		rs=graphRoots[g];
		es1=EdgeList[g];
		es2=Table[s0\[DirectedEdge]n,{n,rs}];
		esp=Join[es2,es1];
		BreadthFirstScan[Graph[esp],s0,{
			"VisitedVertex"->(bfsVisit[#1]&),
			"UnvisitedVertex"->(bfsVisit[#1]&),
			"DiscoverVertex"->(bfsVisit[#1]&)
		}];
		Print[vs];
		Rest@Reverse@DeleteDuplicates@vs
	]

ClearAll[evalCausalGraph]
evalCausalGraph[g_]:=(*
	Propogate causes to effects while scanning the graph breadth first;
	Returns an association list of the values. *)
	Module[{al,evalVertex},
		al=Association[];
		evalVertex[v_]:=
			Module[{w,pav},
				If[KeyExistsQ[al,v]&&!functionQ[al[v]],
				(* then *)al[v],
				(* else, it's cached, if also non-functional*)
					w=PropertyValue[{g,v},value];
				If[Head@w=!=Function,
				(* then *)al[v]=ReleaseHold[w],
				(* else, call the value as a function on the parents *)
					pav=First/@Cases[EdgeList@g,_\[DirectedEdge]v];
				al[v]=(w@@(evalVertex/@pav))
			]]];
		evalVertex/@(VertexList@g);
		al]

ClearAll[setPropertyList]
setPropertyList[g_,p_,is:{_->_,___}]:=(*
	Sets each item's property p to v *)
	Fold[SetProperty[{#1,#2[[1]]},p->#2[[2]]]&,g,is]

ClearAll[functionQ]
	functionQ[expr_]:=
	Head@expr===Function

On@Assert
Check[
	Module[{g1,g2,g3,g3a,g3b,g4,g5},
		g1=PathGraph[{1,2,3,4},DirectedEdges->True];
		g1=setPropertyList[g1,value,(#->#)&/@VertexList@g1];
		Assert[PropertyValue[{g1,#},value]&/@VertexList@g1==VertexList@g1];
		Assert[vertexParents[EdgeList@g1,4]=={3}];
		Assert[graphRoots[g1]=={1}];

		g2=FindSpanningTree@RandomGraph[{10,20},DirectedEdges->True];
		Assert[graphRoots[g2]!={}];

		g3=Graph[{1\[DirectedEdge]0,2\[DirectedEdge]0},VertexLabels->"Name"];
		g3=setPropertyList[g3,value,{1->42,2->5,0->(#1+#2&)}];
		Assert[(0/.evalCausalGraph@g3)==47];

		g3=Graph[{1\[DirectedEdge]0,2\[DirectedEdge]0},VertexLabels->"Name"];

		g3a=setPropertyList[g3,value,{1->0,2->Hold@Random[],0->(#1+#2&)}];
		Assert[(0/.evalCausalGraph@g3a)!=0,
			"Random[] value a sbould be non-zero"];
		g3b=setPropertyList[g3,value,{1->0,2->Hold@Random[],0->(#1+#2&)}];

		Assert[(0/.evalCausalGraph@g3b)!=0,
			"Random[] value b should be non-zero"];
		Assert[(0/.evalCausalGraph@g3a) !=( 0/.evalCausalGraph@g3b),
			"Two Random[]s should not have same value"];

		g4=Graph[{1\[DirectedEdge]0,2\[DirectedEdge]0,3\[DirectedEdge]0}];
		g4=setPropertyList[g4,value,{1->42,2->5,3->1,0->(Plus[##]&)}];
		Assert[(0/.evalCausalGraph@g4)==48];

		(* Graph from Pearl2000 p119 chapter 4 Figure 4.4 *)
		g5=Graph[
		{u1\[DirectedEdge]x1,u1\[DirectedEdge]z,
		x1\[DirectedEdge]u2,x1\[DirectedEdge]z,x1\[DirectedEdge]x2,x1\[DirectedEdge]y,
		u2\[DirectedEdge]z,u2\[DirectedEdge]y,z\[DirectedEdge]x2,x2\[DirectedEdge]y},
		VertexLabels->"Name"];
	    g5=setPropertyList[g5,value,
		{u1->42,x1->(Plus[##]&),x2->(Plus[##]&),y->(Plus[##]&),
		u2->(Plus[##]&),z->(Plus[##]&)}];
		Assert[evalCausalGraph[g5][y]==252];

		(* Same graph based on 10 random values *)
		g5=setPropertyList[g5,value,
		{u1->Hold@RandomInteger[99],x1->(Plus[##]&),x2->(Plus[##]&),
		y->(Plus[##]&),u2->(Plus[##]&),z->(Plus[##]&)}];

		Table[evalCausalGraph@g5,{10}] 
	],
	MessageDialog@"responseRow: selftest failed"]


(* ::Section:: *)
(*Interpret Static Causal Model*)


(* ::Text:: *)
(*A static causal model (gf) is defined by a static influence graph.*)
(**)
(*The following code converts an influence graph ig into generated data having a probability distribution compatible with the ig graph.*)
(*There are binary and general influence graphs.*)
(*A binary influence graph is table of node values v, a list of triples {a,b,r} such that b = a if random < r*)
(*A general influence graph is a table of node values v, a list of arguments args a, and a function f st b *)


(* ::Input:: *)
(**)


(* ::Input::Initialization:: *)
On@Assert

ClearAll[responseRow]
responseRow::template="responseRow[ig,iv]";
responseRow::usage=%<>
	" returns one row of the response cstructure of influence graph " <>   " ig given the prior probabilities iv";
responseRow[ig_(*influenceGraph*),iv_(*initialValues*)]:=
	FixedPoint[edgeScan[#,ig]&,iv]

ClearAll[edgeScan]
edgeScan[v0_,l_] :=(*
	Given the initial node/event state in Held v0 ;
	scan the edges changing the consequent nodes according ;
	to the edge probabilities; *)
	Block[{v=ReleaseHold[v0]}, 
		edge[{a_Integer,b_Integer,r_}]:=(*
			An edge is represented by variables a, b such that a\[Rule]b;
			If b is without value, then set b to Random[] < r when a is true; *)
			v[[b]]=If[v[[b]]=!=True,v[[a]]===True&&Random[]<r,v[[b]]]; 
		edge[{as:{___},b_Integer,f_Function,r_}]:=(*
			General influence diagram *) 
			Module[{args}, 
				args=v[[as]];
				v[[b]]=If[v[[b]]===None,f[args],v[[b]]]];
				Scan[edge[#1]&,l];
				v]

ClearAll[directScan]
directScan[v0_,l_]:=
	Block[{v=ReleaseHold@v0},
	assoc[{pa:{__},b_,f_,r_}]:= (*
	lookup value *)
	v[[b]]=If[v[[b]]===None,
	(*then*)Random[]<r&&f@@v[[pa]],
	(*else*)None];Scan[assoc[#]&,l];
	v]

ClearAll[convertRow]
convertRow[row_]:=
	MapIndexed[If[#1,2*Last@#2-1,2*Last@#2]&,row]
convertRow2[row_]:=
	MapIndexed[If[#1,Last@#2,None]&,row]/.None->Sequence[]

Check[
	Assert[convertRow[{True,True,True,True}]=={1,3,5,7}];
	Assert[convertRow[{True,True,False,False}]=={1,3,6,8}];
	Assert[convertRow2[{True,True,False,True}]=={1,2,4}],
	MessageDialog@"convertRow: selftest failed"]

Check[
	nrows=100;
	ig={{1,2,0.4},{1,4,0.4},{2,3,0.1},{3,4,0.1},{3,6,0.5},{5,6,0.9}};
	(* The initial values are conditional, absolute, or None *)
	iv={Hold@If[Random[]<0.1,True,False],None,None,None,Hold@If[Random[]<0.9,True,False],None};
	rs=Table[responseRow[ig,iv],{nrows}];
	Assert[Length@rs==nrows],
	MessageDialog@"responseRow: selftest failed"]
