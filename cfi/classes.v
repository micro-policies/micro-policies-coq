From mathcomp Require Import ssreflect ssrfun ssrbool eqtype ssrnat.
Require Import common.types.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Class cfi_id mt := {
  id         : eqType;

  word_to_id : mword mt -> option id;
  id_to_word : id -> mword mt;

  id_to_wordK : forall x, word_to_id (id_to_word x) = Some x;
  word_to_idK : forall w x, word_to_id w = Some x -> id_to_word x = w

}.

Section ControlFlow.

Context {mt : machine_types}
        {ids : @cfi_id mt}.

Variable cfg : id -> id -> bool.

Definition valid_jmp w1 w2 :=
  match word_to_id w1, word_to_id w2 with
    | Some id1, Some id2 => cfg id1 id2
    | _, _ => false
  end.

Lemma valid_jmp_true w1 w2 :
  valid_jmp w1 w2 ->
  exists id1 id2,
    word_to_id w1 = Some id1 /\
    word_to_id w2 = Some id2.
Proof.
  unfold valid_jmp.
  intro VALID.
  destruct (word_to_id w1) eqn:W1, (word_to_id w2) eqn:W2;
  try discriminate.
  by eexists; eauto.
Qed.

End ControlFlow.
