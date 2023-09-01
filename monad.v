(* Simple implementation of monads for transition systems.  *)

From mathcomp Require Import all_ssreflect.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Module Monad.

Section Definitions.

Structure law := Law {
  carrier : Type -> Type;
  ret : forall A, A -> carrier A;
  bind : forall A B, (A -> carrier B) -> carrier A -> carrier B;
  _ : forall A B a (f : A -> carrier B), bind f (ret a) = f a;
  _ : forall A ma, bind (@ret A) ma = ma;
  _ : forall A B C ma (f : A -> carrier B) (g : B -> carrier C),
        bind g (bind f ma) = bind (fun a => (bind g (f a))) ma;
  _ : forall A B (f1 f2 : A -> carrier B), f1 =1 f2 -> bind f1 =1 bind f2
  }.

End Definitions.

Module Import Exports.
Coercion carrier : law >-> Funclass.
Arguments ret {_ A} _.
Notation "m >>= f" := (bind f m) (at level 60).
End Exports.

Module Theory.

Section Theory.

Variable M : law.
Variables A B C : Type.
Variables (a : A) (ma: M A) (f f1 f2: A -> M B) (g : B -> M C).

Lemma ret_right_unit_bind :  ret a >>= f  =  f a.
Proof. by case: M f. Qed.

Lemma ret_left_unit_bind :  ma >>= ret  =  ma.
Proof. by case: M ma. Qed.

Lemma bind_assoc :  (ma >>= f) >>= g  =  ma >>= (fun a => f a >>= g).
Proof. by case: M ma f g. Qed.

Lemma bind_ext : f1 =1 f2 -> bind f1 =1 bind f2.
Proof. by case: M A B f1 f2. Qed.

End Theory.

End Theory.
Include Theory.

End Monad.
Export Monad.Exports.

Section FoldM.

Import Monad.

Variable M : law.
Variables A B : Type.
Variable f : A -> B -> M A.

Fixpoint foldm a s := if s is x :: s' then f a x >>= foldm^~ s' else ret a.

Lemma foldm0 a : foldm a [::] = ret a.
Proof. by []. Qed.

Lemma foldm1 a x : foldm a [:: x] = f a x.
Proof. by rewrite /= ret_left_unit_bind. Qed.

Lemma foldm_cat a s1 s2 : foldm a (s1 ++ s2) = foldm a s1 >>= foldm^~ s2.
Proof.
  elim: s1 => [| b s1 IHs1] /= in a *; first by rewrite ret_right_unit_bind.
  rewrite bind_assoc.
  exact: bind_ext.
Qed.

End FoldM.

Prenex Implicits foldm.

Section OptionMonad.

Section Laws.

Variables A B C:Type.

Lemma some_right_unit_obind a (f : A -> option B) : obind f (Some a) = f a.
Proof. by []. Qed.

Lemma some_left_unit_obind oa : obind (@Some A) oa = oa.
Proof. by case: oa. Qed.

Lemma obind_assoc oa (f : A -> option B) (g : B -> option C) :
  obind g (obind f oa) = obind (fun a => (obind g (f a))) oa.
Proof. by case: oa. Qed.

Lemma obind_ext (f1 f2 : A -> option B) : f1 =1 f2 -> obind f1 =1 obind f2.
Proof. by move=> ? []. Qed.

End Laws.

Import Monad.

Canonical option_monad :=
  Law some_right_unit_obind some_left_unit_obind obind_assoc obind_ext.

Lemma foldm_cat_some (A B : Type) f (a0 : A) (s1 s2 : seq B) a2 :
    foldm f a0 (s1 ++ s2) = Some a2 <->
    exists a1, foldm f a0 s1 = Some a1 /\ foldm f a1 s2 = Some a2.
Proof.
  rewrite foldm_cat; split; last by case => [a1 [-> <-]].
  by case: foldm => //= a1 <-; exists a1.
Qed.

Lemma foldm_cons_some (A B : Type) f (a0 : A) t (s : seq B) a2 :
    foldm f a0 (t :: s) = Some a2 <->
    exists a1, f a0 t = Some a1 /\ foldm f a1 s = Some a2.
Proof.
  rewrite -cat1s foldm_cat_some; split.
  - by move=> [a1]; rewrite foldm1 => H; exists a1.
  - by move=> [a1 H]; exists a1; rewrite foldm1.
Qed.

Lemma foldm_rcons_some (A B : Type) f (a0 : A) (s : seq B) t a2 :
    foldm f a0 (rcons s t) = Some a2 <->
    exists a1, foldm f a0 s = Some a1 /\ f a1 t = Some a2.
Proof.
  rewrite -cats1 foldm_cat_some; split.
  - by move=> [a1]; rewrite foldm1 => H; exists a1.
  - by move=> [a1 H]; exists a1; rewrite foldm1.
Qed.

End OptionMonad.

(*
Section FinFunMonad.

Variable aT : finType.

Section Def.

Variable A B : Type.

Definition ffret (a : A) : {ffun aT -> A} := [ffun=> a].
Definition ffbind (f : A -> {ffun aT -> B}) (g : {ffun aT -> A}) : {ffun aT -> B} := [ffun x : aT => f (g x) x].

End Def.

Section Laws.

Variable A B C : Type.

Notation "'M' A" := ({ffun aT -> A}) (at level 100) : type_scope.

Lemma ffret_right_unit_ffbind a (f : A -> M B) :
  ffbind f (ffret a) = f a.
Proof. by apply/ffunP => x; rewrite !ffunE. Qed.

Lemma ffret_left_unit_ffbind ma : ffbind (@ffret A) ma = ma.
Proof. by apply/ffunP => x; rewrite !ffunE. Qed.

Lemma ffbind_assoc ma (f : A -> M B) (g : B -> M C) :
  ffbind g (ffbind f ma) = ffbind (fun a => (ffbind g (f a))) ma.
Proof. by apply/ffunP => x; rewrite !ffunE. Qed.

Lemma ffbind_ext (f1 f2 : A -> M B) :
  f1 =1 f2 -> ffbind f1 =1 ffbind f2.
Proof. by move=> H g; apply/ffunP => x; rewrite !ffunE H. Qed.

End Laws.

Import Monad.

Canonical finfun_monad :=
  Law ffret_right_unit_ffbind ffret_left_unit_ffbind ffbind_assoc ffbind_ext.

End FinFunMonad.
*)

Print LoadPath.