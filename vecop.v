From mathcomp Require Import all_algebra all_ssreflect.
From HB Require Import structures.
Set Implicit Arguments.
Unset Strict Implicit. 
Unset Printing Implicit Defensive.
Import GRing.Theory.

Section Vrot.
Variables (T : Type) (n : nat).

Definition vrot (i : 'I_n.+1) (v : T ^ n.+1) :=
 [ffun j : 'I_n.+1 => v (j + i)%R].
Definition vrotr (i : 'I_n.+1) := vrot (- i)%R.

Lemma vrotrK i : cancel (vrotr i) (vrot i).
Proof. by move=> ?; apply/ffunP=> ?; rewrite !ffunE addrK. Qed.

Lemma vrotK i : cancel (vrot i) (vrotr i).
Proof. by rewrite -{3}[i]opprK; apply: vrotrK. Qed.

Lemma vrot0 v : vrot 0%R v = v.
Proof. by apply/ffunP=> ?; rewrite ffunE addr0. Qed.
 
Lemma vrotr0 v : vrotr 0%R v = v.
Proof. by rewrite /vrotr oppr0 vrot0. Qed.
 
Lemma vrot_vrot m p v : vrot m (vrot p v) = vrot p (vrot m v).
Proof. by apply/ffunP=> ?; rewrite !ffunE addrAC. Qed.
 
Lemma vrot_vrotr m p v : vrot m (vrotr p v) = vrotr p (vrot m v).
Proof. by rewrite vrot_vrot. Qed.
 
Lemma vrotr_vrotr m p v : vrotr m (vrotr p v) = vrotr p (vrotr m v).
Proof. by rewrite /vrotr vrot_vrot. Qed.
 
Lemma forall_vrot P i v: [forall j, P (vrot i v j)] = [forall j, P (v j)].
Proof.
 apply/forallP/forallP=> /[swap] j; last by rewrite ffunE; apply.
 by move/(_ (j - i)%R); rewrite ffunE subrK.
Qed.
 
Lemma forall_vrotr P i v : [forall j, P (vrotr i v j)] = [forall j, P (v j)].
Proof. by rewrite forall_vrot. Qed.
 
Lemma vrot_vrot_add v i j : vrot i (vrot j v) = vrot (i + j)%R v.
Proof. by apply/ffunP=> ?; rewrite !ffunE addrA. Qed.
 
Lemma vrot_vrotr_sub v i j : vrot i (vrotr j v) = vrot (i - j)%R v.
Proof. by rewrite vrot_vrot_add. Qed.
 
Lemma vrotr_vrotr_add v i j : vrotr i (vrotr j v) = vrotr (i + j)%R v.
Proof. by rewrite /vrotr vrot_vrot_add opprD. Qed.
End Vrot.

Section vSub.
Variable dim : nat.
Definition vnat : Type := nat ^ dim.
Definition vint : Type := int ^ dim.

Definition vnat_val (v : vnat) : vint := [ffun i => (v i)%:Z]%R.
Definition vnat_Sub (x : vint) (Px : [forall i, 0 <= x i]%R) :=
 [ffun i => `|x i|%N]%R.

Lemma vnat_SubP (K : vnat -> Type)
     (PK : forall (x : vint) (Px : [forall i, 0 <= x i]%R), K (vnat_Sub Px))
     (u : vnat): K u.
Proof.
 have H i : (0 <= (vnat_val u) i)%R by rewrite ffunE le0z_nat.
 move/forallP in H; move: (PK _ H); rewrite (_ : vnat_Sub H = u) //.
 by apply/ffunP=> ?; rewrite !ffunE.
Qed.

Lemma vnat_SubK (x : vint) (Px : [forall i, (0 <= x i)%R]):
 vnat_val (vnat_Sub Px) = x.
Proof.
 by apply/ffunP=> ?; rewrite !ffunE gez0_abs // (forallP Px).
Qed.

HB.instance Definition _ := isSub.Build _ _ _ vnat_SubP vnat_SubK.

End vSub.

Section ComponetwiseOperation.
Variable aT : finType.
Variables S T R : Type.

(* ret/pure for {ffun aT -> _} *)
Definition ffret (T : Type) (x : T) : {ffun aT -> T} := [ffun=> x].

(* liftM/fmap for {ffun aT -> _} *)
Definition fflift (S T : Type) (f : S -> T) :=
 fun (x : {ffun aT -> S}) => [ffun a => f (x a)].

(* liftM2/liftA2 for {ffun aT -> _} *)
Definition fflift2 (S T R : Type) (op : S -> T -> R) :=
 fun (x : {ffun aT -> S}) (y : {ffun aT -> T}) => [ffun a => op (x a) (y a)].
End ComponetwiseOperation.

Section fflift_Lemma.
Lemma fflift2_vrot (T1 T2 T3 : Type) n i (op : T1 -> T2 -> T3)
 (v1 : T1 ^ n.+1) v2:
 fflift2 op (vrot i v1) (vrot i v2) = vrot i (fflift2 op v1 v2).
Proof. by apply/ffunP=> ?; rewrite !ffunE. Qed.

Lemma fflift2_vrotr (T1 T2 T3 : Type) n i (op : T1 -> T2 -> T3) 
 (v1 : T1 ^ n.+1) v2:
 fflift2 op (vrotr i v1) (vrotr i v2) = vrotr i (fflift2 op v1 v2).
Proof. by apply/ffunP=> ?; rewrite !ffunE. Qed.

Lemma fflift_vrot (T1 T2 : Type) n i (f : T1 -> T2) (v : T1 ^ n.+1) :
 fflift f (vrot i v) = vrot i (fflift f v).
Proof. by apply/ffunP=> ?; rewrite !ffunE. Qed.

Lemma fflift_vrotr (T1 T2 : Type) n i (f : T1 -> T2) (v : T1 ^ n.+1) :
 fflift f (vrotr i v) = vrotr i (fflift f v).
Proof. by apply/ffunP=> ?; rewrite !ffunE. Qed.

Lemma val_vrot n i (s : vnat n.+1) :
 val (vrot i s : vnat n.+1) = vrot i (val s).
Proof. by rewrite -[LHS]/(fflift _ _) fflift_vrot. Qed.

Lemma val_vrotr n i (s : vnat n.+1) :
 val (vrotr i s : vnat n.+1) = vrotr i (val s).
Proof. by rewrite val_vrot. Qed.
End fflift_Lemma.

Section vcat.
Definition vcat (T : Type) (n m : nat) (v : T ^ n) (w : T ^ m) : T ^ (n+m) :=
 [ffun i => match (split i) with inl j => v j | inr k => w k end].
Definition vsplit (T : Type) (n m : nat) (v : T ^ (n + m)) : T ^ n * T ^ m :=
 ([ffun i => v (lshift m i)],[ffun j => v (rshift n j)]).

Lemma vcatK (T : Type) (n m : nat) (v : T ^ n) (w : T ^ m) :
 vsplit (vcat v w) = (v, w). 
Proof.
 rewrite pair_equal_spec; split; apply/ffunP => /= x;rewrite !ffunE;
 case: split_ordP => [j|k].
    by move/lshift_inj => ->.
   by move/eqP; rewrite eq_lrshift.
  by move/eqP; rewrite eq_rlshift.
 by move/rshift_inj => ->.
Qed.

Lemma vsplitK (T : Type) (n m : nat) (v : T ^ (n + m)) :
 vcat (vsplit v).1 (vsplit v).2 = v. 
Proof.
 apply/ffunP =>x; rewrite !ffunE.
 by case: split_ordP => [j|k] ->; rewrite ffunE.
Qed.

Lemma fflift_vcat (T1 T2 : Type) (f : T1 -> T2) m n
 (v1 : T1 ^ m) (v2 : T1 ^ n) :
 fflift f (vcat v1 v2) = vcat (fflift f v1) (fflift f v2).
Proof.
 by apply/ffunP=> ?; rewrite !ffunE; case: splitP => ?; rewrite ffunE.
Qed.  

Lemma fflift2_vcat (T1 T2 T3 : Type) (op : T1 -> T2 -> T3) m n
 (v1 : T1 ^ m) (v2 : T1 ^ n) w1 w2:
 fflift2 op (vcat v1 v2) (vcat w1 w2)
 = vcat (fflift2 op v1 w1) (fflift2 op v2 w2).
Proof.
 by apply/ffunP=> ?; rewrite !ffunE; case: splitP => ?; rewrite ffunE.
Qed.

Lemma forall_vcat (T : Type) (n m : nat) (v : T ^ n) (w : T ^ m) 
 (P : T -> bool) :
 [forall i, P ((vcat v w) i)] = [forall i, P (v i)] && [forall i, P (w i)].
Proof.
 apply/forallP/andP.
  move=> H; split; apply/forallP => i.
   move: (H (lshift m i)); rewrite ffunE.
   by case: split_ordP => ? /eqP; rewrite eq_shift// => /eqP->.
  move: (H (rshift n i)); rewrite ffunE.
  by case: split_ordP => ? /eqP; rewrite eq_shift// => /eqP->.
 case => /forallP /= Pv /forallP /= Pw i.
 by rewrite ffunE; case: splitP => ?.
Qed.

Lemma val_vcat n1 n2 (s1 : vnat n1) (s2 : vnat n2) :
 val (vcat s1 s2 : vnat _) = vcat (val s1) (val s2).
Proof. by rewrite -[LHS]/(fflift _ _) fflift_vcat. Qed.
End vcat.