From mathcomp Require Import all_ssreflect all_algebra all_fingroup finmap zify.
Set Implicit Arguments.
Unset Strict Implicit. 
Unset Printing Implicit Defensive.
Import GRing.Theory Num.Theory.
Require Import vecop monad.
Local Open Scope fset_scope.
Section vtrans.
 
Definition vtrans (dim : nat) (v : vnat dim) (w : vint dim) : option (vnat dim)
 := insub (val v + w)%R.
 
Variable dim : nat.
Lemma vtrans0 (v : vnat dim) : vtrans v 0%R = Some v.
Proof.
 rewrite /vtrans insubT => [|H].
  by apply/forallP=>x; rewrite !ffunE.
 congr Some. apply: val_inj; rewrite SubK.
 by apply/ffunP=>i; rewrite !ffunE; lia.
Qed.

Lemma vtrans_vcat n1 n2 (s1 : vnat n1) (s2 : vnat n2) v1 v2 :
 vtrans (vcat s1 s2) (vcat v1 v2) =
   if (vtrans s1 v1, vtrans s2 v2) is (Some s1', Some s2')
   then Some (vcat s1' s2') else None.
Proof.
 rewrite /vtrans -[(val _ + _)%R]/(fflift2 _ _ _) val_vcat fflift2_vcat.
 case: insubP => [s'|]; rewrite forall_vcat.
   move=> /andP [? ?] vals'; rewrite !insubT; congr Some; apply: val_inj.
   by rewrite vals' val_vcat !SubK.
 by case: insubP => // ? -> _ ?; rewrite insubN.
Qed.

Lemma vtrans_vrot n i (s : vnat n.+1) (v : vint n.+1) :
 vtrans (vrot i s) (vrot i v) = omap (vrot i) (vtrans s v).
Proof.
 rewrite /vtrans -[(_ + _)%R]/(fflift2 _ _ _).
 case: insubP => [s'|]; rewrite val_vrot fflift2_vrot forall_vrot; last first.
  by move=> ?; rewrite insubN.
 move=> ? vals'; rewrite insubT; congr Some; apply: val_inj.
 by rewrite vals' val_vrot SubK.
Qed.

Lemma vtrans_vrotr n i (s : vnat n.+1) (v : vint n.+1) :
 vtrans (vrotr i s) (vrotr i v) = omap (vrotr i) (vtrans s v).
Proof. by rewrite vtrans_vrot. Qed.

Lemma vtrans_add n (s1 s2 s' : vnat n) (v : vint n) :
 vtrans s1 v = Some s' ->
  vtrans (fflift2 addn s1 s2) v = Some (fflift2 addn s' s2).
Proof.
 rewrite /vtrans; case: insubP => // _ /forallP-s1v /[swap] -[->] /ffunP-vals'.
 rewrite insubT => [|s1s2v].
   apply/forallP=> x; move/(_ x): s1v; rewrite !ffunE => s1v.
   by rewrite PoszD addrAC addr_ge0.
 congr Some; apply/ffunP=> x; move/(_ x): vals'; rewrite !ffunE => s'x.
 move/forallP/(_ x): s1s2v; rewrite !ffunE => s1s2v; apply/eqP.
 by rewrite -eqz_nat gez0_abs // PoszD addrAC -s'x.
Qed.
End vtrans.

Section VS.
Variable state : finType.
Variable a b : state -> nat.
Variable f : 'Z_3 -> {perm state}.
Definition vs p i : vnat 3 := vrotr i
 [ffun j : 'Z_3 => if j == 0%R then a (f i p) 
                   else if j == 1%R then b (f i p)
                   else 0].
Definition vst (p q :state) i : vint 3 := vrotr i 
 [ffun j : 'Z_3 => if j == 0%R then - (a (f i p))%:Z 
                   else if j == 1%R then (a (f (i + 1%R) q))%:Z - (b (f i p))%:Z
                   else (b (f (i + 1%R) q))%:Z]%R.
Lemma Z3_cases (i : 'Z_3) : [\/ i = 0, i = 1 | i = 2]%R.
Proof.
 case/SubP: i => -[?|[?|[?|//]]].
  - by constructor 1; apply: val_inj.
  - by constructor 2; apply: val_inj.
  - by constructor 3; apply: val_inj.  
Qed.

End VS.

Section ab_consistent.
Variables (state : finType) (a b : state -> nat).
Local Notation vs := (vs a b).
Local Notation vst := (vst a b).
Definition ab_consistent :=
 forall (f : 'Z_3 -> {perm state}) (p p' q : state) (i i' : 'Z_3),
 vtrans (vs f p i) (vst f p' q i') =  
 if (p' == p) && (i' == i) then Some (vs f q (i + 1)%R) else None.
Definition ab_consistent0 := 
 forall (f : 'Z_3 -> {perm state}) (p p' q : state) (i : 'Z_3),
 vtrans (vs f p 0%R) (vst f p' q i) = 
 if (p' == p) && (i == 0%R) then Some (vs f q 1%R) else None. 
Definition ab_aligned := 
 injective a 
 /\ (forall p q : state, a p > a q -> forall r : state, a r + b p < b q)
 /\ forall p q : state, a p < b q.


Lemma consis_to_consis0 (f : 'Z_3 -> {perm state}) (p p' q : state) (i i' : 'Z_3) :
 vtrans (vs f p i) (vst f p' q i') = 
 omap (vrotr i) (vtrans (vs (fun j => f (j+i)%R) p 0%R) (vst (fun j => f (j+i)%R) p' q (i' - i)%R)).
Proof.
 rewrite -vtrans_vrotr /vs vrotr0 !add0r; congr (vtrans _ _).
 apply: (canRL (vrotK i)).
 rewrite /vst vrot_vrotr_sub /vrotr opprD opprK addrC.
 by rewrite (addrAC _ 1%R) subrK.
Qed.

Lemma ab_consis_consis0 : ab_consistent <-> ab_consistent0.
Proof.
 split; first by move=> ?.
 move=> H_vs0 f p p' q i i'; rewrite consis_to_consis0.
 rewrite H_vs0 subr_eq0; case: ifP => //= _; congr Some.
 by rewrite /vs vrotr_vrotr_add addrC.
Qed.

Lemma ab_aligned_consis0 : ab_aligned -> ab_consistent0.
Proof.
 rewrite /ab_consistent0 /ab_aligned => -[inj_a [a_gt_bpbq a_gt_b]] f p p' q i. 
 case: ifP.
  move/andP => [/eqP -> /eqP ->].
  rewrite /vtrans; case: insubP=> [w|].
   move/forallP => H1 H2; congr Some.
   apply: val_inj; rewrite H2; apply/ffunP=> k; rewrite !ffunE add0r.
   by case: (Z3_cases k) => -> /=; lia.
  rewrite negb_forall; move/existsP=> -[j].
  rewrite !ffunE.
  by case: (Z3_cases j) => -> /=; lia.
 move/negP/negP; rewrite Bool.negb_andb; move/orP=> H.
 rewrite /vtrans insubN // negb_forall. 
 apply/existsP; move: H; case: (Z3_cases i) => [-> []|-> _|-> _] //.
   case: (ltngtP (a (f 0%R p)) (a (f 0%R p'))) => [h _|h _|].
      by exists 0%R; rewrite !ffunE /=; lia.
     by exists 1%R; rewrite !ffunE add0r /=; move: (a_gt_bpbq _ _ h (f 1%R q)); lia.
    by move/inj_a/perm_inj=> ->; rewrite eqxx.
  exists 2%R; rewrite !ffunE add0r /=; move: (a_gt_b (f 2%R q) (f 1%R p')).
  by rewrite -[(1+1)%R]/(2%R); lia.
 case E: (a (f 2%R p')) => [|n];last by exists 2%R; rewrite !ffunE /=; lia.
 exists 0%R; rewrite !ffunE /= (_ : (2 + 1)%R = 0%R);last by apply:eqP.
 case E': (a (f 0%R q)) => [|m].
  by move: (a_gt_b (f 0%R p) (f 2%R p')); lia.
 have h : a (f 2%R p') < a (f 0%R q) by rewrite E E'.
 move: (a_gt_b (f 0%R q) (f 0%R q)) (a_gt_bpbq (f 0%R q) (f 2%R p') h (f 0%R p)).
 by lia.
Qed.


Lemma ab_aligned_consis :ab_aligned -> ab_consistent.
Proof.
 by move => H_ab; rewrite ab_consis_consis0; apply: ab_aligned_consis0.
Qed.

Lemma injective_a : ab_consistent -> injective a.
Proof. 
 pose f (_ : 'Z_3): {perm state} := 1%g.
 move => /ab_consis_consis0 /(_ f) H_vs0 p q.
 wlog le_bqp : p q / b p <= b q => [Hb|ap_aq].
  case: (orP (leq_total (b p) (b q))) => /Hb // Ha /esym apaq. 
  by apply: esym; apply: Ha.
 have: vtrans (vs f q 0%R) (vst f p p 0%R) = 
 Some (fflift2 addn (vs f p 1%R) (finfun_of_tuple [tuple 0;b q - b p; 0])).
  suff -> : (vs f q 0%R) = (fflift2 addn (vs f p 0%R) 
  (finfun_of_tuple [tuple 0;b q - b p; 0])).
   by apply: vtrans_add; rewrite H_vs0 !eqxx. 
  apply/ffunP=> x; rewrite !ffunE subr0.
  by case: (Z3_cases x) => -> /=; rewrite ?addn0 /f ?perm1 ?subnKC. 
 by rewrite H_vs0 andbT; case: eqP.
Qed.

Lemma inc_a_dec_b : ab_consistent -> forall p q : state, a p > a q -> 
 (forall r : state, (a r + b p)%N < b q).
Proof.
 pose f (_ : 'Z_3): {perm state} := 1%g.
 move => /ab_consis_consis0 /(_ f) H_vs0 p q ap_aq r.
 move: (H_vs0 p q r 0%R); rewrite /vtrans.
 case: insubP => [w|];last first.
  rewrite negb_forall; move/existsP=> -[i].
  rewrite !ffunE.
  by case: (Z3_cases i) => -> /=; rewrite /f ?perm1; lia.
 move/forallP => k.
 case: ifP => // H /[swap] -[->].
 by move/ffunP => /(_ 0%R); rewrite !ffunE subrr sub0r /tnth /f !perm1 /=; lia.
Qed.

Lemma ap_lt_bq :  #|state| > 1 -> ab_consistent -> 
 forall p q : state, a p < b q.
Proof.
 pose f (_ : 'Z_3) : {perm state} := 1%g.
 move => /card_gt1P H  H_vs p q. move: H => -[r [r']] [_ _].
  wlog app' : r r' / a r < a r' => [H|];last first.
   move: (H_vs f r q p 1%R 2%R); rewrite andbF /vtrans /vs /vst !perm1.
   case: insubP => [//|].
   rewrite negb_forall; move/existsP=> -[i].
   rewrite !ffunE; case: (Z3_cases i) => -> //=. lia.
   by case/negP; move: (inc_a_dec_b H_vs app' q); lia.
 case: (ltngtP (a r) (a r'));first by apply: H.
  by rewrite eq_sym; apply: H.
 by move/injective_a ->; rewrite ?eqxx.
Qed.

Lemma ab_consis_aligned : #|state| > 1 -> ab_consistent -> ab_aligned.
Proof.
 move => H1 H_vs; repeat split.
   exact: injective_a.
  exact: inc_a_dec_b.
 exact: ap_lt_bq.
Qed.

Lemma consis_aligned_iff : #|state| > 1 -> ab_consistent <-> ab_aligned.
Proof.
 move=> H; split.
  exact: (ab_consis_aligned H).
 exact: ab_aligned_consis.
Qed.
End ab_consistent.

Section VAS.
Variable dim : nat.
Definition VAS := {fset (vint dim)}.
Definition markingVAS : Type := vnat dim.
Definition nextVAS {vas : VAS} (m : markingVAS) (v : vas) : option markingVAS 
 := vtrans m (val v).
End VAS.

Section VASS.
Variables (dim : nat) (state : finType).
Definition VASS  := {fset (state * vint dim * state)}.
Definition confVASS : Type := state * vnat dim.
Definition nextVASS {vass : VASS} (c : confVASS) (a : vass) 
 : option confVASS := let: (q1,v,q2) := val a in
  let: (q,m) := c in
   if q1 == q then 
    if vtrans m v is Some t then Some (q2, t) else None
  else None.
End VASS.

Section VASS2VAS.
Variables (dim : nat) (state : finType) (vass : VASS dim state).
Variable a b : state -> nat.
Variable f : 'Z_3 -> {perm state}.
Hypothesis hypo_ab : ab_aligned a b.
Local Notation vs := (vs a b f).
Local Notation vst := (vst a b f).
  
Definition VAS_of_VASS_m (c : confVASS dim state) : (markingVAS (dim + 3)) :=
 let: (q, m) := c in vcat m (vs q 0%R).
Definition VAS_of_VASS_01 (b' : bool) (q : state) 
 : vint (dim + 3) := vcat (0%R : vint dim) (vst q q (b'%:R)%R).
Definition VAS_of_VASS_2 (p q : state) (v : vint dim)
 : vint (dim + 3) := vcat v (vst p q 2%R).
Definition VAS_of_VASS_t : VAS (dim+3) := 
 [fset VAS_of_VASS_01 b' q | b' : bool, q : state] 
 `|` [fset let: (p,v,q) := t in VAS_of_VASS_2 p q v | t in vass].

Definition reachable {S T : Type} (next : S -> T -> option S) (x0 x : S) :=
 exists s : seq T, foldm next x0 s = Some x.
 
Lemma vtransE_vs (p p' q : state) (i i': 'Z_3) : 
 vtrans (vs p i) (vst p' q i') =  
 if (p' == p) && (i' == i) then Some (vs q (i + 1)%R) else None.
Proof. by rewrite (ab_aligned_consis hypo_ab). Qed.

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
 have T2 : VAS_of_VASS_2 q'' q' v \in VAS_of_VASS_t.
  apply/fsetUP; right; apply/imfsetP => /=. 
  by exists (val x); [apply: valP|rewrite E].
 exists (t' ++ [:: [` T1 false]; [` T1 true]; [` T2]]).
 rewrite foldm_cat_some; exists (VAS_of_VASS_m (q'', m'')); split => //. 
 rewrite /= /nextVAS /= vtrans_vcat vtransE_vs vtrans0 !eqxx /=.
 rewrite vtrans_vcat vtransE_vs vtrans0 !eqxx /=.
 rewrite vtrans_vcat vtransE_vs E' H' !eqxx /=.
 by rewrite -oppr0.
 (*by rewrite (_ : (2 + 1)%R = 0%R);last by apply:eqP. *)
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
 rewrite (_ : (2 + 1)%R = 0%R);last by apply:eqP. 
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