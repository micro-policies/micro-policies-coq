(* Definition of symbolic rules and tags used for kernel protection,
   along with conversion functions towards concrete integer tags.

   Here are the various kinds of tags we use:

     For the PC:

     - KERNEL          : for kernel mode

     - USER ut is_call : for user mode. [ut] gives the user-level tag,
       while flag [is_call] signals whether we've just executed a JAL,
       for keeping track of system calls.

     For registers:

     - KERNEL : for data only used in the kernel

     - USER ut false : for data only used in user mode, with
       corresponding user-level tag [ut]

     For memory:
     - KERNEL : for kernel space
     - USER [ut] false : similar to above
     - ENTRY : for system call entry points

*)

Require Import List Arith Bool.
Require Import ZArith.
Import ListNotations.
Require Import Coq.Classes.SetoidDec.
Require Coq.Vectors.Vector.

Require Import common concrete utils Coqlib.
Import DoNotation.
Import Concrete.

Set Implicit Arguments.

Section rules.

Variable user_tag : Type.
Variable tnone : user_tag.
Context {equ : EqDec (eq_setoid user_tag)}.

Open Scope nat_scope.

Definition nfields (op : opcode) : option (nat * nat) :=
  match op with
  | NOP => Some (0, 0)
  | CONST => Some (1, 1)
  | MOV => Some (2, 1)
  | BINOP _ => Some (3, 1)
  | LOAD => Some (3, 1)
  | STORE => Some (3, 1)
  | JUMP => Some (1, 0)
  | BNZ => Some (1, 0)
  | JAL => Some (2, 1)
  | _ => None
  end.

Inductive tag : Type :=
| USER (ut : user_tag) (is_call : bool)
| KERNEL
| ENTRY.

Global Instance tag_eq_dec : EqDec (eq_setoid tag).
  intros t1 t2.
  refine (
      match t1, t2 with
      | USER ut1 b1, USER ut2 b2 =>
        match ut1 == ut2, b1 == b2 with
        | left H1, left H2 => _
        | _, _ => _
        end
      | KERNEL, KERNEL
      | ENTRY, ENTRY => left eq_refl
      | _, _ => _
      end
    ); simpl in *; subst; solve [left; congruence | right; congruence].
Defined.

Definition is_user (t : tag) : bool :=
  match t with
  | USER _ _ => true
  | _ => false
  end.

Definition is_user_data (t : tag) : bool :=
  match t with
  | USER _ is_call => negb is_call
  | _ => false
  end.

Definition is_call (t : tag) : bool :=
  match t with
  | USER _ is_call => is_call
  | _ => false
  end.

Variable TNONE : tag.
Definition TCOPY := TNONE.

Definition mvec_fields T (fs : option (nat * nat)) : Type :=
  match fs with
  | Some fs => Vector.t T (fst fs)
  | None => Empty_set
  end.

Record MVec T : Type := mkMVec {
  op  : opcode;
  tpc : T;
  ti  : T;
  ts  : mvec_fields T (nfields op)
}.

Record RVec T : Type := mkRVec {
  trpc : T;
  tr   : T
}.

(* Returns true iff an opcode can only be executed by the kernel *)
Definition privileged_op (op : opcode) : bool :=
  match op with
  | JUMPEPC
  | ADDRULE
  | GETTAG
  | PUTTAG => true
  | _ => false
  end.

Definition rule := (MVec tag * RVec tag)%type.
Definition rules := list rule.


Definition masks : Masks :=
  let mk_mask dcm cm :=
      let '(dcm_tcp,dcm_ti,dcm_t1,dcm_t2,dcm_t3) := dcm in
      let '(cm_trpc,cm_tr) := cm in
      Build_Mask
        (fun mvp =>
           match mvp with
             | mvp_tpc => dcm_tcp
             | mvp_ti => dcm_ti
             | mvp_t1 => dcm_t1
             | mvp_t2 => dcm_t2
             | mvp_t3 => dcm_t3
           end)
         (mkCTMask cm_trpc cm_tr) in
  fun kernel opcode =>
    if kernel then
      match opcode with
        | NOP => mk_mask (false,false,true,true,true) (Some mvp_tpc,None)
        | CONST =>  mk_mask (false,false,true,true,true) (Some mvp_tpc,None)
        | MOV => mk_mask (false,false,true,true,true) (Some mvp_tpc,Some mvp_t1)
        | BINOP _ => mk_mask (false,false,true,true,true) (Some mvp_tpc,None)
        | LOAD =>  mk_mask (false,false,true,true,true) (Some mvp_tpc,Some mvp_t2)  (* unclear whether copy-through is useful, but seems harmless enough *)
        | STORE => mk_mask (false,false,true,true,true) (Some mvp_tpc,Some mvp_t2)
        | JUMP => mk_mask (false,false,true,true,true) (Some mvp_t1,None)
        | BNZ => mk_mask (false,false,true,true,true) (Some mvp_tpc,None)
        | JAL => mk_mask (false,false,true,true,true) (Some mvp_t1,Some mvp_tpc)
        | JUMPEPC => mk_mask (false,false,true,true,true) (Some mvp_t1,None)
        | ADDRULE => mk_mask (false,false,true,true,true) (Some mvp_tpc,None)
        | GETTAG => mk_mask (false,false,true,true,true) (Some mvp_tpc,None)
        | PUTTAG => mk_mask (false,false,true,true,true) (Some mvp_tpc,None)
      end
    else
      match opcode with
        | NOP => mk_mask (false,false,true,true,true) (None,None)
        | CONST =>  mk_mask (false,false,false,true,true) (None,None)
        | MOV => mk_mask (false,false,false,false,true) (None,None)
        | BINOP _ => mk_mask (false,false,false,false,false) (None,None)
        | LOAD =>  mk_mask (false,false,false,false,false) (None,None)
        | STORE => mk_mask (false,false,false,false,false) (None,None)
        | JUMP => mk_mask (false,false,false,true,true) (None,None)
        | BNZ => mk_mask (false,false,false,true,true) (None,None)
        | JAL => mk_mask (false,false,false,false,true) (None,None)
        | JUMPEPC => mk_mask (false,false,true,true,true) (None,None)
        | ADDRULE => mk_mask (false,false,true,true,true) (None,None)
        | GETTAG => mk_mask (false,false,false,false,true) (None,None)
        | PUTTAG => mk_mask (false,false,false,false,false) (None,None)
      end
.

Section handler.

Context {t : machine_types}.
Context {cp : concrete_params t}.
Context {ops : machine_ops t}
        {sp : machine_ops_spec ops}.

(* TODO: Define the operations below in terms of a concrete encoding
   for tags. *)

Class encodable := {
  encode : tag -> word t;
  decode : word t -> option tag;
  decodeK : forall t, decode (encode t) = Some t;
  encodeK : forall t w, decode w = Some t -> encode t = w
}.

Context {e : encodable}.

Lemma encode_inj t1 t2 :
  encode t1 = encode t2 -> t1 = t2.
Proof.
  intros E.
  cut (Some t1 = Some t2); try congruence.
  rewrite <- (decodeK t1).
  rewrite <- (decodeK t2).
  congruence.
Qed.

Definition word_lift (P : tag -> bool) (w : word t) : bool :=
  match decode w with
  | Some t => P t
  | None => false
  end.

Lemma word_lift_impl P Q w :
  (forall t, P t = true -> Q t = true) ->
  word_lift P w = true -> word_lift Q w = true.
Proof.
  unfold word_lift.
  intros I H.
  destruct (decode w) as [t'|]; eauto.
Qed.

Import DoNotation.

Variable uhandler : MVec user_tag -> option (RVec user_tag).

Definition encode_fields (fs : option (nat * nat)) : mvec_fields tag fs -> Vector.t (word t) 3 :=
  match fs return mvec_fields tag fs -> Vector.t (word t) 3 with
  | Some fs => fun v =>
                 let get n :=
                     match nth_error (Vector.to_list v) n with
                     | Some t => encode t
                     | None => Concrete.TNone
                     end in
                 Vector.of_list [get 0; get 1; get 2]
  | None => fun v => match v with end
  end.

Definition encode_mvec (mvec : MVec tag) : Concrete.MVec (word t) :=
  let f n := Vector.nth (encode_fields _ (ts mvec)) n in
  {|
    Concrete.cop := op_to_word (op mvec);
    Concrete.ctpc := encode (tpc mvec);
    Concrete.cti := encode (ti mvec);
    Concrete.ct1 := f Fin.F1;
    Concrete.ct2 := f (Fin.FS Fin.F1);
    Concrete.ct3 := f (Fin.FS (Fin.FS Fin.F1))
  |}.

Definition decode_mvec (cmvec : Concrete.MVec (word t)) : option (MVec tag) :=
  do op  <- word_to_op (Concrete.cop cmvec);
  do tpc <- decode (Concrete.ctpc cmvec);
  do ti  <- decode (Concrete.cti cmvec);
  do ts  <- match nfields op as fs return option (mvec_fields tag fs) with
            | Some fs =>
              match fst fs as n return option (Vector.t tag n) with
              | 0 => Some (Vector.nil _)
              | S n' =>
                do t1 <- decode (Concrete.ct1 cmvec);
                match n' return option (Vector.t tag (S n')) with
                | 0 => Some (Vector.of_list [t1])
                | S n'' =>
                  do t2 <- decode (Concrete.ct2 cmvec);
                  match n'' return option (Vector.t tag (S (S n''))) with
                  | 0 => Some (Vector.of_list [t1; t2])
                  | S n''' =>
                    do t3 <- decode (Concrete.ct3 cmvec);
                    Some (Vector.cons _ t1 _ (Vector.cons _ t2 _ (Vector.const t3 _)))
                  end
                end
              end

            | None => None
            end;
     Some (mkMVec op tpc ti ts).

Lemma decode_mvecK (mvec : MVec tag) :
  decode_mvec (encode_mvec mvec) = Some mvec.
Proof.
  unfold decode_mvec, encode_mvec.
  destruct mvec as [op tpc ti ts]. simpl.
  rewrite op_to_wordK. simpl.
  repeat rewrite decodeK. simpl.
  destruct op; simpl in *;
  repeat (
      match goal with
      | ts : Empty_set |- _ => destruct ts
      | ts : Vector.t tag 0 |- _ => induction ts using Vector.case0
      | ts : Vector.t tag (S _) |- _ => induction ts using caseS
      | |- context[decode (encode _)] => rewrite decodeK
      end; simpl; eauto
  ).
Qed.

Lemma encode_mvec_inj mvec1 mvec2 :
  encode_mvec mvec1 = encode_mvec mvec2 ->
  mvec1 = mvec2.
Proof.
  intros H.
  cut (Some mvec1 = Some mvec2); try congruence.
  repeat rewrite <- decode_mvecK.
  congruence.
Qed.

Lemma eq_tag_eq_word t1 t2 :
  (encode t1 ==b encode t2) = (t1 ==b t2).
Proof.
  destruct (t1 ==b t2) eqn:E.
  - rewrite eqb_true_iff in E.
    rewrite eqb_true_iff. congruence.
  - rewrite eqb_false_iff in E.
    rewrite eqb_false_iff.
    contradict E.
    now apply encode_inj.
Qed.

Definition encode_rvec (rvec : RVec tag) : Concrete.RVec (word t) :=
  {|
    Concrete.ctrpc := encode (trpc rvec);
    Concrete.ctr := encode (tr rvec)
  |}.

Definition ground_rules : Concrete.rules (word t) :=
  let mk op := Concrete.mkMVec (op_to_word op) (encode KERNEL) (encode KERNEL)
                               (encode TNONE) (encode TNONE) (encode TNONE) in
  [
   (mk NOP, Concrete.mkRVec (encode TCOPY) (encode TNONE));
   (mk CONST, Concrete.mkRVec (encode TCOPY) (encode KERNEL));
   (mk MOV, Concrete.mkRVec (encode TCOPY) (encode TCOPY));
   (mk (BINOP ADD), Concrete.mkRVec (encode TCOPY) (encode KERNEL));
   (mk (BINOP SUB), Concrete.mkRVec (encode TCOPY) (encode KERNEL));
   (mk (BINOP MUL), Concrete.mkRVec (encode TCOPY) (encode KERNEL));
   (mk (BINOP EQ),  Concrete.mkRVec (encode TCOPY) (encode KERNEL));
   (mk LOAD, Concrete.mkRVec (encode TCOPY) (encode TCOPY));
   (mk STORE, Concrete.mkRVec (encode TCOPY) (encode TCOPY));
   (mk JUMP, Concrete.mkRVec (encode TCOPY) (encode TNONE));
   (mk BNZ, Concrete.mkRVec (encode TCOPY) (encode TNONE));
   (mk JAL, Concrete.mkRVec (encode TCOPY) (encode TCOPY));
   (mk JUMPEPC, Concrete.mkRVec (encode TCOPY) (encode TNONE));
   (mk ADDRULE, Concrete.mkRVec (encode TCOPY) (encode TNONE));
   (mk GETTAG, Concrete.mkRVec (encode TCOPY) (encode KERNEL));
   (mk PUTTAG, Concrete.mkRVec (encode TCOPY) (encode TNONE))
  ].

Definition mvec_of_umvec (call : bool) (mvec : MVec user_tag) : MVec tag :=
  match mvec with
  | mkMVec op tpc ti ts =>
    mkMVec op (USER tpc call) (USER ti false)
           (match nfields op as fs return mvec_fields user_tag fs ->
                                          mvec_fields tag fs
            with
            | Some fs => fun ts => Vector.map (fun t => USER t false) ts
            | None => fun ts => ts
            end ts)
  end.

Definition rvec_of_urvec (op : opcode) (rvec : RVec user_tag) : RVec tag :=
  let call := match op with JAL => true | _ => false end in
  {| trpc := USER (trpc rvec) call;
     tr   := USER (tr rvec) false |}.

(* This is the handler that should be implemented concretely by the
   fault handler. Notice that this only takes care of the tagging
   behavior on regular user instructions, and doesn't include anything
   about system calls. *)

Definition handler (mvec : MVec tag) : option (RVec tag) :=
  match mvec with
  | mkMVec op (USER tpc _) (USER ti false) ts =>
    let process ts :=
        do rvec <- uhandler (mkMVec op tpc ti ts);
        Some (rvec_of_urvec op rvec) in
    match nfields op as fs return (mvec_fields user_tag fs -> option (RVec tag)) ->
                                  mvec_fields tag fs -> option (RVec tag) with
    | Some fs =>
      fun process ts =>
        do ts <- sequence (Vector.map (fun t =>
                                         match t with
                                         | USER t false => Some t
                                         | _ => None
                                       end)
                                      ts);
        process ts
    | None => fun _ ts => match ts with end
    end process ts
  | _ => None
  end.

End handler.

End rules.

Arguments ENTRY {user_tag}.
Arguments KERNEL {user_tag}.
