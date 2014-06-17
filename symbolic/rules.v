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

Require Import List Arith Bool ZArith. Import ListNotations.
Require Coq.Vectors.Vector.

Require Import ssreflect ssrfun ssrbool eqtype ssrnat.

Require Import lib.Coqlib lib.utils common.common concrete.concrete symbolic.symbolic.
Import DoNotation.
Import Concrete.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Section rules.

Variable user_tag : eqType.
Variable tnone : user_tag.

Open Scope nat_scope.

Inductive tag : Type :=
| USER (ut : user_tag) (is_call : bool)
| KERNEL
| ENTRY.

Definition tag_eq u v :=
  match u, v with
    | USER ut1 b1, USER ut2 b2 => (ut1 == ut2) && (b1 == b2)
    | KERNEL, KERNEL
    | ENTRY, ENTRY => true
    | _, _ => false
  end.

Lemma tag_eqP : Equality.axiom tag_eq.
Proof.
move=> [ut1 b1||] [ut2 b2||] /=; try by apply: (iffP idP).
apply: (iffP andP) => [[]|[<- <-]] //.
by repeat move/eqP->.
Qed.

Definition tag_eqMixin := EqMixin tag_eqP.
Canonical tag_eqType := Eval hnf in EqType tag tag_eqMixin.

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
  encodeK : forall t w, decode w = Some t -> encode t = w;
  encode_kernel_tag : Concrete.TKernel = encode KERNEL
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

Variable uhandler : Symbolic.MVec user_tag -> option (Symbolic.RVec user_tag).

Definition encode_fields (fs : option (nat * nat)) : Symbolic.mvec_operands tag fs -> Vector.t (word t) 3 :=
  match fs return Symbolic.mvec_operands tag fs -> Vector.t (word t) 3 with
  | Some fs => fun v =>
                 let get n :=
                     match nth_error (Vector.to_list v) n with
                     | Some t => encode t
                     | None => Concrete.TNone
                     end in
                 Vector.of_list [get 0; get 1; get 2]
  | None => fun v => match v with end
  end.

Definition encode_mvec (mvec : Symbolic.MVec tag) : Concrete.MVec (word t) :=
  let f n := Vector.nth (encode_fields (Symbolic.ts mvec)) n in
  {|
    Concrete.cop := op_to_word (Symbolic.op mvec);
    Concrete.ctpc := encode (Symbolic.tpc mvec);
    Concrete.cti := encode (Symbolic.ti mvec);
    Concrete.ct1 := f Fin.F1;
    Concrete.ct2 := f (Fin.FS Fin.F1);
    Concrete.ct3 := f (Fin.FS (Fin.FS Fin.F1))
  |}.

Definition decode_mvec (cmvec : Concrete.MVec (word t)) : option (Symbolic.MVec tag) :=
  do! op  <- word_to_op (Concrete.cop cmvec);
  do! tpc <- decode (Concrete.ctpc cmvec);
  do! ti  <- decode (Concrete.cti cmvec);
  do! ts  <- match Symbolic.nfields op as fs return option (Symbolic.mvec_operands tag fs) with
            | Some fs =>
              match fst fs as n return option (Vector.t tag n) with
              | 0 => Some (Vector.nil _)
              | S n' =>
                do! t1 <- decode (Concrete.ct1 cmvec);
                match n' return option (Vector.t tag (S n')) with
                | 0 => Some (Vector.of_list [t1])
                | S n'' =>
                  do! t2 <- decode (Concrete.ct2 cmvec);
                  match n'' return option (Vector.t tag (S (S n''))) with
                  | 0 => Some (Vector.of_list [t1; t2])
                  | S n''' =>
                    do! t3 <- decode (Concrete.ct3 cmvec);
                    Some (Vector.cons _ t1 _ (Vector.cons _ t2 _ (Vector.const t3 _)))
                  end
                end
              end

            | None => None
            end;
     Some (Symbolic.mkMVec op tpc ti ts).

Lemma decode_mvecK (mvec : Symbolic.MVec tag) :
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
  (encode t1 == encode t2) = (t1 == t2).
Proof.
by rewrite (inj_eq encode_inj).
Qed.

Definition encode_rvec (rvec : Symbolic.RVec tag) : Concrete.RVec (word t) :=
  {|
    Concrete.ctrpc := encode (Symbolic.trpc rvec);
    Concrete.ctr := encode (Symbolic.tr rvec)
  |}.

Lemma encode_rvec_inj rvec1 rvec2 :
  encode_rvec rvec1 = encode_rvec rvec2 ->
  rvec1 = rvec2.
Proof.
  destruct rvec1, rvec2.
  unfold encode_rvec. simpl.
  intros H. inv H.
  f_equal; apply encode_inj; trivial.
Qed.

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

Definition mvec_of_umvec (call : bool) (mvec : Symbolic.MVec user_tag) : Symbolic.MVec tag :=
  match mvec with
  | Symbolic.mkMVec op tpc ti ts =>
    Symbolic.mkMVec op (USER tpc call) (USER ti false)
           (match Symbolic.nfields op as fs return Symbolic.mvec_operands user_tag fs ->
                                          Symbolic.mvec_operands tag fs
            with
            | Some fs => fun ts => Vector.map (fun t => USER t false) ts
            | None => fun ts => ts
            end ts)
  end.

Definition rvec_of_urvec (op : opcode) (rvec : Symbolic.RVec user_tag) : Symbolic.RVec tag :=
  let call := match op with JAL => true | _ => false end in
  {| Symbolic.trpc := USER (Symbolic.trpc rvec) call;
     Symbolic.tr   := USER (Symbolic.tr rvec) false |}.

(* This is the handler that should be implemented concretely by the
   fault handler. Notice that this only takes care of the tagging
   behavior on regular user instructions, and doesn't include anything
   about system calls. *)

Definition handler (mvec : Symbolic.MVec tag) : option (Symbolic.RVec tag) :=
  match mvec with
  | Symbolic.mkMVec op (USER tpc _) (USER ti false) ts =>
    let process ts :=
        do! rvec <- uhandler (Symbolic.mkMVec op tpc ti ts);
        Some (rvec_of_urvec op rvec) in
    match Symbolic.nfields op as fs return (Symbolic.mvec_operands user_tag fs -> option (Symbolic.RVec tag)) ->
                                  Symbolic.mvec_operands tag fs -> option (Symbolic.RVec tag) with
    | Some fs =>
      fun process ts =>
        do! ts <- sequence (Vector.map (fun t =>
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

