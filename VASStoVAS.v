From mathcomp Require Import all_ssreflect all_algebra finmap zify.
Set Implicit Arguments.
Unset Strict Implicit. 
Unset Printing Implicit Defensive.
Import GRing.Theory.
Require Import vecop vectrans monad.
Local Open Scope fset_scope.

Section VAS.
Variable dim : nat.
Definition VAS := {fset (vint dim)}.
Definition markingVAS : Type := vnat dim.
Definition nextVAS {vas : VAS} (m: markingVAS) (v : vas) 
 : option markingVAS := vtrans m (val v).
End VAS.

Section VASS.
Variables (dim : nat) (state : finType).
Definition VASS  := {fset (state * vint dim * state)}.
Definition confVASS : Type := state * vnat dim.
Definition nextVASS {vass : VASS} (c : confVASS) (a : vass) 
 : option confVASS := let: (q1,v,q2) := val a in
  let: (q,m) := c in
   if q1 != q then None
   else if vtrans m v isn't Some t then None
        else Some (q2, t).
End VASS.

Section VASS2VAS.
Variables (dim : nat) (state : finType) (vass : VASS dim state).
Variable a b : state -> nat.
Hypothesis hypo_ab : vtrans_ab a b.
Local Notation vs := (vs a b).
Local Notation vst := (vst a b).
  
Definition VAS_of_VASS_m (c : confVASS dim state) : (markingVAS (dim + 3)) :=
 let: (q, m) := c in vcat m (vs q 0%R).
Definition VAS_of_VASS_01 (b' : bool) (q : state) 
 : vint (dim + 3) := vcat (0%R : vint dim) (vst q q (b'%:R)%R).
Definition VAS_of_VASS_2 (p : state) (v : vint dim) (q : state) 
 : vint (dim + 3) := vcat v (vst p q 2%R).
Definition VAS_of_VASS_t : VAS (dim+3) := 
 [fset VAS_of_VASS_01 b' q | b' : bool, q : state] 
 `|` [fset let: (p,v,q) := t in VAS_of_VASS_2 p v q | t in vass].

Definition reachable {S T : Type} (next : S -> T -> option S) (x0 x : S) :=
 exists s : seq T, foldm next x0 s = Some x.
 
Lemma vtransE_vs (p p' q : state) (i i': 'Z_3) : 
 vtrans (vs p i) (vst p' q i') =  
 if (p' == p) && (i' == i) then Some (vs q (i + 1)%R) else None.
Proof. by rewrite (vtrans_ab_vs hypo_ab). Qed.

Lemma vs_inj (q q' : state) (i i' : 'Z_3) :
 vs q i = vs q' i' -> q = q' /\ i = i'.
Proof.
 move/(congr1 (@vtrans 3 ^~ (vst q q i))); rewrite !vtransE_vs !eqxx /=.
 by case: ifP => // /andP [/eqP -> /eqP ->].
Qed.

Lemma VAS_of_VASS_reachable (c0 c : confVASS dim state) :
 reachable (@nextVASS _ _ vass) c0 c -> 
 reachable (@nextVAS _ VAS_of_VASS_t) (VAS_of_VASS_m c0) (VAS_of_VASS_m c).
Proof.
 case=> s; elim/last_ind: s => [|s' x IH] in c *.
  by case => ->; exists [::].
 rewrite foldm_rcons_some => -[[q'' m'']] [/IH] {IH}.
 case: c => [q' m'] [t'] Ht'; case E: (val x) => [[p v] p'] /[dup] H.
 rewrite /nextVASS E; move: E; case: ifP => // /eqP -> /[swap].
 case E': (vtrans m'' v) => [w|//] [-> H'] E.
 have T1 (b' : bool) : VAS_of_VASS_01 b' q'' \in VAS_of_VASS_t.
  by rewrite !inE; apply/orP; left; rewrite in_imfset2.
 have T2 : VAS_of_VASS_2 q'' v q' \in VAS_of_VASS_t.
  apply/fsetUP; right; apply/imfsetP => /=. 
  by exists (val x); [apply: valP|rewrite E].
 exists (t' ++ [:: [` T1 false]; [` T1 true]; [` T2]]).
 rewrite foldm_cat_some; exists (VAS_of_VASS_m (q'', m'')); split => //. 
 rewrite /= /nextVAS /= vtrans_vcat vtransE_vs vtrans0 !eqxx /=.
 rewrite vtrans_vcat vtransE_vs vtrans0 !eqxx /=.
 by rewrite vtrans_vcat vtransE_vs E' H' !eqxx /=.
Qed.
 
Lemma VASS_of_VAS_reachable' (c0 : confVASS dim state) (vm : markingVAS (dim+3)) :
 reachable (@nextVAS _ VAS_of_VASS_t) (VAS_of_VASS_m c0) vm ->
 exists q m i, vm = vcat m (vs q i) /\ reachable (@nextVASS _ _ vass) c0 (q,m).
Proof.
 case => t; elim/last_ind: t => [|s x IH] in vm *.
  case: c0 => [q0 m0]. case=> <-; exists q0, m0, 0%R; split => //. 
  by exists [::].
 rewrite foldm_rcons_some /nextVAS => -[vm'] [].
 move/IH => -[q' [m' [i]]] [-> H_reach] {IH}.
 case/fsetUP: (valP x).
  case/imfset2P => /= b' _ [r _] ->.
  rewrite /VAS_of_VASS_01 vtrans_vcat vtrans0 vtransE_vs.
  case: ifP => // /andP [/eqP -> /eqP <-] [<-].
  by exists q', m', ((b'%:R) + 1)%R.
 case/imfsetP => /= v Hv ->. case E: v => /= [pm q''].
 case: pm => p m'' in E *.
 rewrite vtrans_vcat vtransE_vs.
 case E': vtrans => [m|//]. move: E => /[swap].
 case: ifP => // /andP [/eqP -> /eqP <-] [] <- E.
 exists q'',m,0%R; split => //.
 case: H_reach=> t Ht.
 exists (rcons t [` Hv]).
 rewrite foldm_rcons_some; exists (q', m');split => //.
 by rewrite /nextVASS /= E eqxx E'. 
Qed.
 
Lemma VASS_of_VAS_reachable (c0 c: confVASS dim state) :
 reachable (@nextVAS _ VAS_of_VASS_t) (VAS_of_VASS_m c0) (VAS_of_VASS_m c) ->
 reachable (@nextVASS _ _ vass) c0 c.
Proof. 
 case: c => q m /VASS_of_VAS_reachable' [q' [m' [i []]]].
 rewrite /VAS_of_VASS_m.
 move/(congr1 (@vsplit _ _ _)). rewrite !vcatK => -[<-].
 by move/vs_inj => [->].
Qed.

Lemma reachable_VASS_VAS (c0 c: confVASS dim state) :
 reachable (@nextVASS _ _ vass) c0 c <-> 
 reachable (@nextVAS _ VAS_of_VASS_t) (VAS_of_VASS_m c0) (VAS_of_VASS_m c).
Proof. 
 split; first exact: VAS_of_VASS_reachable.
 exact: VASS_of_VAS_reachable.
Qed.

End VASS2VAS.

Section VASS2VAS_Example.
Variable state : finType.
Definition a_q (q : state) : nat := (enum_rank q).+1.
Definition b_q (q : state) : nat := #|state|.+1 * (#|state| - enum_rank q).
Local Notation a := a_q.
Local Notation b := b_q.

Lemma ab_prop : vtrans_ab a b.
Proof.
 repeat split.
   by move=> p q; move/eq_add_S => /ord_inj /enum_rank_inj.
  move=> p q /[swap] r; rewrite /a /b => aq_ap.
  apply: (@leq_trans (#|state|.+1 * (#|state| - enum_rank p).+1)).
   by rewrite mulnS ltn_add2r ltnS.
  by rewrite leq_pmul2l ?ltn_sub2l // ltnS ltnW.
 move=> p q; rewrite /a /b.
 apply: (@leq_trans (#|state|.+1)). 
  by rewrite ltnS.
 by rewrite leq_pmulr ?subn_gt0 // ltnS ltnW.
Qed.
End VASS2VAS_Example.

Section minab.
Variable state : finType.
Variable a b : state -> nat.
Hypothesis H_ab : vtrans_ab a b.

Definition mina (q : state) : nat := enum_rank q.
Definition minb (q : state) : nat := #|state| * (#|state| - enum_rank q).

Lemma minab_prop : vtrans_ab mina minb.
Proof.
 repeat split; first by move=> p q /ord_inj /enum_rank_inj.
  move=> p q /[swap] r; rewrite /mina => ap_aq.
  apply: (@leq_trans (#|state| * (#|state| - enum_rank p).+1)).
   by rewrite mulnS ltn_add2r.
  by rewrite leq_pmul2l ?ltn_sub2l //; apply/card_gt0P; exists p.
 move=> p q; rewrite /mina.
 apply: (@leq_trans (#|state|)) => //. 
 by rewrite leq_pmulr ?subn_gt0.
Qed.

Definition sorted_state := sort (relpre a leq) (enum state).
Definition sorted_a := map a sorted_state.
Definition sorted_b := map b sorted_state.
 
Lemma a_is_sorted : sorted ltn sorted_a.
Proof.
 rewrite /sorted_a /sorted_state ltn_sorted_uniq_leq -sort_map.
 rewrite sort_uniq (map_inj_uniq H_ab.1) enum_uniq.
 by rewrite (sort_sorted leq_total).
Qed. 

Lemma size_state : size sorted_state = #|state|.
Proof. by rewrite size_sort -cardT. Qed.

Lemma nth_sorted (q : state) (f : state -> nat) (n k : nat) :
 n < #|state| -> nth 0 [seq f q | q <- sorted_state] n 
 = f (nth q sorted_state n).
Proof.
 by move=> ?; apply: nth_map; rewrite size_state. 
Qed.

Lemma a_ith_geq : forall i, i < #|state| -> i <= nth 0 sorted_a i.
Proof.
 move=> i; rewrite /sorted_a.
 elim: i => [//|k IHk /[dup]].
 move/leqW/IHk/[swap]; move: a_is_sorted; rewrite /sorted_a.
 move/(sortedP 0)/(_ k); rewrite size_map size_sort cardT => /[apply] /[swap].
 by apply: leq_ltn_trans.
Qed.

Lemma b_ith_geq : forall i, i < #|state| ->
 #|state| * (#|state| - i) <= nth 0 sorted_b i.
Proof.
 rewrite /sorted_b => i i_state.
 rewrite -{2}(@subKn i #|state|) -?(@subnSK i #|state|) ?(ltnW i_state) //.
 move: i_state => /(leq_ltn_trans (leq0n _)) /[dup] gt0s /card_gt0P [q _].
 pose argmaxa := nth q sorted_state #|state|.-1.
 have Hk : #|state|.-1 <= a argmaxa.
  move: (@a_ith_geq #|state|.-1); rewrite ltn_predL => /(_ gt0s).
  by rewrite -subn1 (nth_sorted q) ?subn1 ?ltn_predL.
 have H : #|state| - i.+1 < #|state| by rewrite ltn_subrL.
 elim : (#|state| - i.+1) => [|n IHn] in H *.
  rewrite muln1 (nth_sorted q) ?subn1 ?ltn_predL // -{1}(ltn_predK gt0s).
  by apply: leq_ltn_trans Hk (H_ab.2.2 _ _).
  move: (ltnW H) => /[dup] Hn /IHn.
 rewrite !(nth_sorted q) ?ltn_subrL //.
 move/(leq_add Hk) => IHk.
 rewrite mulnS -{1}(ltn_predK gt0s) addSnnS addnS.
 rewrite (leq_ltn_trans IHk) ?H_ab.2.1 //.
 move/(sortedP 0)/(_ (#|state| - n.+2)) : a_is_sorted.
 rewrite size_map size_state.
 rewrite subnSK // !(nth_sorted q) ?ltn_subrL //.
 by apply.
Qed.

End minab.