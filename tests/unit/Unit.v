From ITree Require Import
     ITree ITreeFacts.

Import CatNotations.
Local Open Scope cat.

(* Test that we can indeed rewrite handlers under interp.  *)
Lemma interp_id_id {E R} (t : itree E R) :
  interp (id_ E >>> id_ E) t ≈ t.
Proof.
  rewrite (fold_apply_IFun (interp _)).
  rewrite cat_id_r.
  rewrite <- fold_apply_IFun.
  rewrite interp_id_h.
  reflexivity.
Qed.

Parameter IO : Type -> Type.
Parameter exit : forall {a}, IO a.
Declare Instance Monad_IO : Monad IO.
Declare Instance MonadIter_IO : MonadIter IO.

Definition execute {E T} (m : itree E T) : IO T :=
  interp (M := IO) (fun _ _ => exit) m.
