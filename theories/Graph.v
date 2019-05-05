From Coq.NArith Require Import NArith.
From Coq.Structures Require Import OrderedTypeEx.
From Coq.FSets Require Import FMapList FSetList.
From CoLoR.Util Require Import FGraph.FGraph.

Require Import Reduction.

Module NSet := FSetList.Make N_as_OT.
Module NMap := FMapList.Make N_as_OT.

Module NGraph := FGraph.Make NSet NMap.

(* Coercion NGraph.rel : NGraph.graph >-> NGraph.relation_on_X. *)

Definition undirected (g : NGraph.graph) :=
  forall x y, NGraph.rel g x y -> NGraph.rel g y x.

Definition undirected_graph :=
  { g : NGraph.graph | undirected g }.

Definition nset_size (s : NSet.t) : nat :=
  NSet.fold (fun _ n => S n) s 0.

(* size of graph = |V| + |E| *)
Definition graph_size (g : NGraph.graph) : nat :=
  NMap.fold (fun _ succs n => n + 1 + nset_size succs) g 0.
