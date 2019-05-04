Require Import Coq.Lists.List.
Require Import Coq.NArith.NArith.
Require Import Coq.Classes.SetoidTactics.
Require Import Coq.Classes.Morphisms Coq.Classes.Morphisms_Prop.
Require Export Coq.Classes.RelationClasses Coq.Relations.Relation_Definitions.
Require Import Coq.Classes.Equivalence Coq.Program.Basics.

From Hardness Require Import CNFSAT Graph Reduction.
From Hardness Require Natnat.

Import ListNotations.

Definition sized_clique (g : NGraph.graph) (k : nat) : Prop :=
  exists (vs : NSet.t),
    nset_size vs = k /\
    forall v1 v2,
      NSet.In v1 vs ->
      NSet.In v2 vs ->
      NGraph.rel g v1 v2.

Instance CLIQUE : problem (undirected_graph * N) :=
  {| ProblemSize := fun '(g, k) => (graph_size (proj1_sig g) + N.to_nat (N.size k))%nat;
     ProblemYes := fun '(g, k) => sized_clique (proj1_sig g) (N.to_nat k);
  |}.

Definition unwrap_or {A} : A -> option A -> A :=
  option_rect (fun _ => A) (fun x => x).

Definition combine_neighbors' (vs1 vs2 : option NSet.t) : NSet.t :=
  NSet.union (unwrap_or NSet.empty vs1) (unwrap_or NSet.empty vs2).

Definition combine_neighbors (vs1 vs2 : option NSet.t) : option NSet.t :=
  Some (combine_neighbors' vs1 vs2).

Definition merge_graphs : NGraph.graph -> NGraph.graph -> NGraph.graph :=
  NMap.map2 combine_neighbors.

Lemma merge_graphs_correct : forall g1 g2 v1 v2,
    NGraph.rel (merge_graphs g1 g2) v1 v2 <-> (NGraph.rel g1 v1 v2 \/ NGraph.rel g2 v1 v2).
Proof.
  unfold merge_graphs, NGraph.rel.
  intros.
  split; intro H.
  - destruct H as [vs [H1 H2]].
    match goal with
    | [ _ : ?x = Some _ |- _ ] =>
      assert (x <> None) as H3 by congruence
    end.
    rewrite <-NGraph.M.XMapFacts.in_find_iff in H3.
    apply NMap.map2_2 in H3.
    apply NMap.map2_1 with (f := combine_neighbors) in H3.
    rewrite H1 in H3.
    cbv [combine_neighbors combine_neighbors'] in H3.
    inversion H3; clear H3; subst.
    destruct NMap.find, NMap.find; cbv [unwrap_or option_rect] in *.
    + apply NSet.union_1 in H2.
      destruct H2; eauto.
    + rewrite NGraph.S.union_empty_r in H2.
      eauto.
    + rewrite NGraph.S.union_empty_l in H2.
      eauto.
    + cbn in H2.
      rewrite NGraph.S.union_empty_l in H2.
      apply NGraph.S.XSetFacts.empty_iff in H2.
      intuition.
  - destruct H as [[vs [H1 H2]] | [vs [H1 H2]]].
    + exists (combine_neighbors' (Some vs) (NMap.find v1 g2)).
      split.
      * rewrite NMap.map2_1.
        -- cbv [combine_neighbors].
           now rewrite H1.
        -- left.
           apply NGraph.M.XMapFacts.in_find_iff.
           congruence.
      * cbv [combine_neighbors' unwrap_or option_rect].
        now apply NSet.union_2.
    + exists (combine_neighbors' (NMap.find v1 g1) (Some vs)).
      split.
      * rewrite NMap.map2_1.
        -- cbv [combine_neighbors].
           now rewrite H1.
        -- right.
           apply NGraph.M.XMapFacts.in_find_iff.
           congruence.
      * cbv [combine_neighbors' unwrap_or option_rect].
        now apply NSet.union_3.
Qed.

Definition edge (v1 v2 : N * N) : NGraph.graph :=
  let v1' := Natnat.encodeN v1 in
  let v2' := Natnat.encodeN v2 in
  NGraph.add_edge v1' v2' NMap.empty.

Definition undirected_edge (v1 v2 : N * N) : NGraph.graph :=
  merge_graphs (edge v1 v2) (edge v2 v1).

Definition undirected (g : NGraph.graph) :=
  forall x y, NGraph.rel g x y -> NGraph.rel g y x.

Import NGraph.R.

Lemma undirected_edge_undirected : forall v1 v2,
    undirected (undirected_edge v1 v2).
Proof.
  intros v1 v2 x y.
  cbv [undirected_edge edge].
  intros H.
  apply merge_graphs_correct in H.
  apply merge_graphs_correct.
  destruct H.
  - apply NGraph.rel_add_edge in H.
    assert (NGraph.rel NMap.empty U NGraph.id (Natnat.encodeN v1) (Natnat.encodeN v2) == NGraph.id (Natnat.encodeN v1) (Natnat.encodeN v2)) as H0.
    { now rewrite NGraph.rel_empty, RelUtil.union_empty_l. }
    apply H0 in H.
    cbv [NGraph.id] in H; intuition subst.
    right.
    apply NGraph.rel_add_edge.
    assert (NGraph.rel NMap.empty U NGraph.id (Natnat.encodeN v2) (Natnat.encodeN v1) == NGraph.id (Natnat.encodeN v2) (Natnat.encodeN v1)) as H1.
    { now rewrite NGraph.rel_empty, RelUtil.union_empty_l. }
    apply H1.
    cbv [NGraph.id].
    auto.
  - apply NGraph.rel_add_edge in H.
    assert (NGraph.rel NMap.empty U NGraph.id (Natnat.encodeN v2) (Natnat.encodeN v1) == NGraph.id (Natnat.encodeN v2) (Natnat.encodeN v1)) as H0.
    { now rewrite NGraph.rel_empty, RelUtil.union_empty_l. }
    apply H0 in H.
    cbv [NGraph.id] in H; intuition subst.
    left.
    apply NGraph.rel_add_edge.
    assert (NGraph.rel NMap.empty U NGraph.id (Natnat.encodeN v1) (Natnat.encodeN v2) == NGraph.id (Natnat.encodeN v1) (Natnat.encodeN v2)) as H1.
    { now rewrite NGraph.rel_empty, RelUtil.union_empty_l. }
    apply H1.
    cbv [NGraph.id].
    auto.
Qed.

Fixpoint edges_for_lit_cl (cl : clause) (cl_name : N) (lit : literal) (v : N * N) : NGraph.graph * N :=
  match cl with
  | nil => (NMap.empty, 0)
  | lit' :: cl' =>
    let '(edges, l_name) := edges_for_lit_cl cl' cl_name lit v in
    match lit, lit' with
    | PosLit v1, NegLit v2
    | NegLit v1, PosLit v2 =>
      if N.eq_dec v1 v2
      then (edges, l_name + 1)
      else (merge_graphs (undirected_edge (cl_name, l_name) v) edges, l_name + 1)
    | _, _ =>
      (merge_graphs (undirected_edge (cl_name, l_name) v) edges, l_name + 1)
    end
  end.

Lemma edges_for_lit_cl_correct : forall cl cl_name lit v,
    let '(g, _) := edges_for_lit_cl cl cl_name lit v in
    undirected g.
Proof.
  induction cl; cbn; intros cl_name lit v.
  - intros x y H.
    apply NGraph.rel_empty in H.
    inversion H.
  - 

Fixpoint edges_for_lit (f : cnf_formula) (lit : literal) (v : N * N) : NGraph.graph * N :=
  match f with
  | nil => (NMap.empty, 0)
  | cl :: f' =>
    let '(edges, cl_name) := edges_for_lit f' lit v in
    let '(lit_edges, _) := edges_for_lit_cl cl cl_name lit v in
    (merge_graphs edges lit_edges, cl_name + 1)
  end.

Fixpoint edges_for_clause (f : cnf_formula) (cl : clause) (cl_name : N) : NGraph.graph * N :=
  match cl with
  | nil => (NMap.empty, 0)
  | l :: cl' =>
    let '(edges, l_name) := edges_for_clause f cl' cl_name in
    let '(new_edges, _) := edges_for_lit f l (cl_name, l_name) in
    (merge_graphs edges new_edges, l_name + 1)
  end.

Fixpoint do_the_thing (f : cnf_formula) : NGraph.graph * N :=
  match f with
  | nil => (NMap.empty, 0)
  | cl :: f' =>
    let '(g, n) := do_the_thing f' in
    let '(edges, _) := edges_for_clause f' cl n in
    (merge_graphs g edges, n + 1)
  end.

(* Definition cnfsat_to_clique (f : cnf_formula) : NGraph.graph * N := *)
(*   () *)