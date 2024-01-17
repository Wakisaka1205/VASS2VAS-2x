From mathcomp Require Import all_ssreflect all_algebra all_fingroup finmap zify.
Set Implicit Arguments.
Unset Strict Implicit. 
Unset Printing Implicit Defensive.
Import GRing.Theory Num.Theory.
Require Import vecop.

Section vtrans.
Definition vtrans (dim : nat) (v : vnat dim) (w : vint dim) : option (vnat dim)
 := insub (val v + w)%R.
 
Variable dim : nat.
Lemma vtrans0 (v : vnat dim) : vtrans v 0%R = Some v.
Proof.
 rewrite /vtrans insubT => [|H].
  by apply/forallP=> ?; rewrite !ffunE.
 congr Some; apply: val_inj; rewrite SubK.
 by apply/ffunP=> ?; rewrite !ffunE addr0.
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
Variables (state : finType) (a b : state -> nat).
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
 by rewrite /vst vrot_vrotr_sub /vrotr opprD opprK addrC (addrAC _ 1%R) subrK.
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
 move=> -[inj_a [a_gt_bpbq a_gt_b]] f p p' q i.
 case: ifP => [/andP [/eqP -> /eqP ->]|/negP /negP].
  rewrite /vtrans; case: insubP=> [w /forallP _ Hw|].
   congr Some; apply: val_inj.
   rewrite Hw; apply/ffunP=> k; rewrite !ffunE add0r.
   by case: (Z3_cases k) => -> /=; lia.
  rewrite negb_forall; move/existsP=> -[j]; rewrite !ffunE.
  by case: (Z3_cases j) => -> /=; lia.
 rewrite Bool.negb_andb; move/orP => NH.
 rewrite /vtrans insubN // negb_forall.
 apply/existsP; move: NH; case: (Z3_cases i) => [-> []|-> _|-> _] //.
   case: (ltngtP (a (f 0%R p)) (a (f 0%R p'))) => [h _|h _|].
      by exists 0%R; rewrite !ffunE /=; lia.
     by exists 1%R; rewrite !ffunE add0r /=; move: (a_gt_bpbq _ _ h (f 1%R q)); lia.
    by move/inj_a/perm_inj=> ->; rewrite eqxx.
  exists 2%R; rewrite !ffunE add0r /=; move: (a_gt_b (f 2%R q) (f 1%R p')).
  by rewrite -[(1+1)%R]/(2%R); lia.
 case E: (a (f 2%R p')) => [|n]; last by exists 2%R; rewrite !ffunE /=; lia.
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
 have : vtrans (vs f q 0%R) (vst f p p 0%R) = 
   Some (fflift2 addn (vs f p 1%R) (finfun_of_tuple [tuple 0;b q - b p; 0])).
  suff -> : (vs f q 0%R) = 
            (fflift2 addn (vs f p 0%R) (finfun_of_tuple [tuple 0;b q - b p; 0])).
   by apply: vtrans_add; rewrite H_vs0 !eqxx.
  apply/ffunP=> x; rewrite !ffunE subr0.
  by case: (Z3_cases x) => -> /=; rewrite ?addn0 /f ?perm1 ?subnKC. 
 by rewrite H_vs0 andbT; case: eqP.
Qed.

Lemma inc_a_dec_b : ab_consistent -> 
 forall p q : state, a p > a q -> (forall r : state, (a r + b p)%N < b q).
Proof.
 pose f (_ : 'Z_3): {perm state} := 1%g.
 move => /ab_consis_consis0 /(_ f) H_vs0 p q ap_aq r.
 move: (H_vs0 p q r 0%R); rewrite /vtrans.
 case: insubP => [w|]; last first.
  rewrite negb_forall; move/existsP=> -[i]; rewrite !ffunE.
  by case: (Z3_cases i) => -> /=; rewrite /f ?perm1; lia.
 move/forallP => k; case: ifP => // H /[swap] -[->].
 by move/ffunP => /(_ 0%R); rewrite !ffunE subrr sub0r /tnth /f !perm1 /=; lia.
Qed.

Lemma ap_lt_bq :  #|state| > 1 -> ab_consistent -> 
 forall p q : state, a p < b q.
Proof.
 pose f (_ : 'Z_3): {perm state} := 1%g.
 move/card_gt1P => -[p [p']] [_ _ H] H_vs r q; move: H.
  wlog app' : p p' / a p < a p' => [WH|]; last first.
   move: (H_vs f p q r 1%R 2%R); rewrite andbF /vtrans.
   case: insubP => [//|].
   rewrite negb_forall; move/existsP=> -[i]; rewrite !ffunE /f !perm1.
   case: (Z3_cases i) => -> //=. lia.
   by case/negP; move: (inc_a_dec_b H_vs app' q); lia.
  case: (ltngtP (a p) (a p')); first by apply: WH.
  by rewrite eq_sym; apply: WH.
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