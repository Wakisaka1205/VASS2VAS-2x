From mathcomp Require Import all_ssreflect all_algebra finmap zify.
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
Definition vs p i : vnat 3 := vrotr i 
 (finfun [fun _: 'Z_3 => a p with 1%R |-> b p, 2%R |-> 0]).
Definition vst (p q :state) i : vint 3 := vrotr i 
 (finfun [fun _: 'Z_3 => - (a p)%:Z with 1%R |-> (a q)%:Z - (b p)%:Z, 
                                         2%R |-> (b q)%:Z]%R).

Lemma Z3_cases (i : 'Z_3) : [\/ i = 0, i = 1 | i = 2]%R.
Proof.
 case/SubP: i => -[?|[?|[?|//]]].
  - by constructor 1; apply: val_inj.
  - by constructor 2; apply: val_inj.
  - by constructor 3; apply: val_inj.  
Qed.

End VS.

Section vtrans_vs.
Variables (state : finType) (a b : state -> nat).
Definition vtrans_vs :=
 forall (p p' q : state) (i i' : 'Z_3),
 vtrans (vs a b p i) (vst a b p' q i') =  
 if (p' == p) && (i' == i) then Some (vs a b q (i + 1)%R) else None.
Definition vtrans_vs0 := 
 forall (p p' q : state) (i : 'Z_3),
 vtrans (vs a b p 0%R) (vst a b p' q i) = 
 if (p' == p) && (i == 0%R) then Some (vs a b q 1%R) else None. 
Definition vtrans_ab := 
 injective a 
 /\ (forall p q : state, a p > a q -> forall r : state, a r + b p < b q)
 /\ forall p q : state, a p < b q.
  
Lemma vtrans_to_vs0 (p p' q : state) (i i' : 'Z_3) :
 vtrans (vs a b p i) (vst a b p' q i') = 
 omap (vrotr i) (vtrans (vs a b p 0%R) (vst a b p' q (i' - i)%R)).
Proof.
 rewrite -vtrans_vrotr /vs vrotr0; congr (vtrans _ _). 
 apply: (canRL (vrotK i)).
 by rewrite /vst vrot_vrotr_sub /vrotr opprD opprK addrC.
Qed.

Lemma vtrans_vs0_vs : vtrans_vs0 <-> vtrans_vs.
Proof.
 split; last by move=>H p p' q i; rewrite (H p p' q (0%R : 'Z_3) i).
 move=> H_vs0 p p' q i i'.
 rewrite vtrans_to_vs0.
 apply: (canLR (omapK (vrotK i))).
 rewrite H_vs0 subr_eq0; case: ifP => //= _; congr Some.
 by rewrite /vs vrot_vrotr_sub opprD addrA subrr sub0r.
Qed.
 
Lemma vtrans_ab_vs0 : vtrans_ab -> vtrans_vs0.
Proof.
 rewrite /vtrans_vs0 /vtrans_ab => -[inj_a [a_gt_bpbq a_gt_b]] p p' q i. 
 case: ifP.
  move/andP => [/eqP <- /eqP ->].
  rewrite /vtrans; case: insubP=> [w|].
   move/forallP => H1 H2; congr Some.
   apply: val_inj; rewrite H2; apply/ffunP=> k; rewrite !ffunE.
   by case: (Z3_cases k) => -> /=; lia.
  rewrite negb_forall; move/existsP=> -[j].
  rewrite !ffunE.
  by case: (Z3_cases j) => -> /=; lia.
 move/negP/negP; rewrite Bool.negb_andb; move/orP=> H.
 rewrite /vtrans insubN // negb_forall. 
 apply/existsP; move: H; case: (Z3_cases i) => [-> []|-> _|-> _] //.
   case: (ltngtP (a p) (a p')) => [h _|h _|h].
      by exists 0%R; rewrite !ffunE /=; lia.
     by exists 1%R; rewrite !ffunE /=; move: (a_gt_bpbq _ _ h q); lia.
    by move: (inj_a _ _ h)=> ->; rewrite eqxx.
  by exists 2%R; rewrite !ffunE /=; move: (a_gt_b q p'); lia.
 case E: (a p') => [|n];last by exists 2%R; rewrite !ffunE /=; lia.
 exists 0%R; rewrite !ffunE /=.
 case E': (a q) => [|m]; first by move: (a_gt_b p p'); lia.
 have h : a p' < a q by rewrite E E'.
 by move: (a_gt_b q q) (a_gt_bpbq q p' h p); lia.
Qed.

Lemma vtrans_ab_vs :vtrans_ab -> vtrans_vs.
Proof.
 by move => H_ab; rewrite -vtrans_vs0_vs; apply: vtrans_ab_vs0.
Qed.

Lemma injective_a : vtrans_vs -> injective a.
Proof. 
 move => /vtrans_vs0_vs H_vs0 p q.
 wlog le_bqp : p q / b p <= b q => [Hb|ap_aq].
  case: (orP (leq_total (b p) (b q))) => /Hb // Ha /esym apaq. 
  by apply: esym; apply: Ha.
 have: vtrans (vs a b q 0%R) (vst a b p p 0%R) = 
 Some (fflift2 addn (vs a b p 1%R) (finfun_of_tuple [tuple 0;b q - b p; 0])).
  suff -> : (vs a b q 0%R) = (fflift2 addn (vs a b p 0%R) 
  (finfun_of_tuple [tuple 0;b q - b p; 0])).
   by apply: vtrans_add; rewrite H_vs0 !eqxx. 
  apply/ffunP=> x; rewrite !ffunE subr0.
  by case: (Z3_cases x) => -> /=; rewrite ?addn0 ?subnKC. 
 by rewrite H_vs0 andbT; case: eqP.
Qed.

Lemma inc_a_dec_b : vtrans_vs -> forall p q : state, a p > a q -> 
 (forall r : state, (a r + b p)%N < b q).
Proof.
 rewrite -vtrans_vs0_vs => H_vs0 p q ap_aq r.
 move: (H_vs0 p q r 0%R); rewrite /vtrans.
 case: insubP => [w|];last first.
  rewrite negb_forall; move/existsP=> -[i].
  rewrite !ffunE.
  by case: (Z3_cases i) => -> /=; lia.
 move/forallP => k.
 case: ifP => // H /[swap] -[->].
 by move/ffunP => /(_ 0%R); rewrite !ffunE subrr sub0r /tnth /=; lia.
Qed.

Lemma ap_lt_bq :  #|state| > 1 -> vtrans_vs -> 
 forall p q : state, a p < b q.
Proof.
 move => /card_gt1P H  H_vs r q. move: H => -[p [p']] [_ _].
  wlog app' : p p' / a p < a p' => [H|];last first.
   move: (H_vs p q r 1%R 2%R); rewrite andbF /vtrans.
   case: insubP => [//|].
   rewrite negb_forall; move/existsP=> -[i].
   rewrite !ffunE; case: (Z3_cases i) => -> //=. lia.
   case/negP. 
   move: (inc_a_dec_b H_vs app' q); lia.
 case: (ltngtP (a p) (a p'));first by apply: H.
  by rewrite eq_sym; apply: H.
 by move/injective_a ->; rewrite ?eqxx.
Qed.

Lemma vtrans_vs_ab : #|state| > 1 -> vtrans_vs -> vtrans_ab.
Proof.
 move => H1 H_vs; repeat split.
   exact: injective_a.
  exact: inc_a_dec_b.
 exact: ap_lt_bq.
Qed.

Lemma vtrans_iff : #|state| > 1 -> vtrans_vs <-> vtrans_ab.
Proof.
 move=> H; split.
  exact: (vtrans_vs_ab H).
 exact: vtrans_ab_vs.
Qed.
End vtrans_vs.