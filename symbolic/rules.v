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

Require Import ssreflect ssrfun ssrbool eqtype ssrnat.

Require Import lib.hlist lib.Coqlib lib.Integers lib.utils common.common concrete.concrete symbolic.symbolic.
Import DoNotation.
Import Concrete.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Section tag.

Variable user_tag : eqType.

Open Scope nat_scope.

Inductive tag : Type :=
| USER (ut : user_tag)
| KERNEL
| ENTRY (sct : user_tag).

Definition tag_eq u v :=
  match u, v with
    | USER ut1, USER ut2 => ut1 == ut2
    | KERNEL, KERNEL => true
    | ENTRY sct1, ENTRY sct2 => sct1 == sct2
    | _, _ => false
  end.

Lemma tag_eqP : Equality.axiom tag_eq.
Proof.
move=> [ut1| |sct1] [ut2| |sct2] /=;
try (by apply: (iffP idP));
apply: (iffP eqP) => [|[<-]] //;
congruence.
Qed.

Definition tag_eqMixin := EqMixin tag_eqP.
Canonical tag_eqType := Eval hnf in EqType tag tag_eqMixin.

Definition is_user (t : tag) : bool :=
  match t with
  | USER _ => true
  | _ => false
  end.

Definition is_entry_tag (t : tag) : bool :=
  match t with
  | ENTRY _ => true
  | _ => false
  end.

(* Returns true iff an opcode can only be executed by the kernel *)
Definition privileged_op (op : opcode) : bool :=
  match op with
  | JUMPEPC
  | ADDRULE
  | GETTAG
  | PUTTAG => true
  | _ => false
  end.

End tag.

Arguments ENTRY {user_tag} _.
Arguments KERNEL {user_tag}.

(*
Definition rule := (MVec tag * RVec tag)%type.
Definition rules := list rule.
*)

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
        | HALT => mk_mask (false,false,false,false,false) (None,None)
        | SERVICE => mk_mask (false,false,false,false,false) (None,None)
      end
    else
      (* CH: at least this part should be a parameter the policy
         programmer can set differently for each policy *)
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
        | HALT => mk_mask (false,false,false,false,false) (None,None)
        | SERVICE => mk_mask (false,false,false,false,false) (None,None)
      end.

Section encoding.

Context (t : machine_types).

(* TODO: Define the operations below in terms of a concrete encoding
   for tags. *)

Class encodable ut := {
  decode : word t -> word_map t (atom (word t) (word t)) -> tag ut;
  decode_kernel_tag : forall m, decode Concrete.TKernel m = KERNEL
}.

End encoding.

Section tag_encoding.

Context (t : machine_types)
        (tty : Symbolic.tag_kind -> eqType)
        (et : forall tk, encodable t (tty tk)).

Local Notation wrapped_tag := (fun tk => [eqType of tag (tty tk)]).

Variable transfer : forall ivec : Symbolic.IVec tty, option (Symbolic.OVec tty (Symbolic.op ivec)).

Definition decode_fields (fs : list Symbolic.tag_kind) (ts : word t * word t * word t)
                         (m : word_map t (atom (word t) (word t)))
                         : option (hlist wrapped_tag fs) :=
  match fs return option (hlist wrapped_tag fs) with
  | [] => Some tt
  | k1 :: fs' =>
    let t1 := decode (fst (fst ts)) m in
    match fs' return option (hlist wrapped_tag (k1 :: fs')) with
    | [] => Some (t1, tt)
    | k2 :: fs'' =>
      let t2 := decode (snd (fst ts)) m in
      match fs'' return option (hlist wrapped_tag (k1 :: k2 :: fs'')) with
      | [] => Some (t1, (t2, tt))
      | k3 :: fs''' =>
        let t3 := decode (snd ts) m in
        match fs''' return option (hlist wrapped_tag (k1 :: k2 :: k3 :: fs''')) with
        | [] => Some (t1, (t2, (t3, tt)))
        | _ :: _ => None
        end
      end
    end
  end.

Definition decode_ivec (mvec : Concrete.MVec (word t))
                       (m : word_map t (atom (word t) (word t)))
                       : option (Symbolic.IVec wrapped_tag) :=
  do! op  <- word_to_op (Concrete.cop mvec);
  let tpc := decode (Concrete.ctpc mvec) m in
  let ti  := decode (Concrete.cti mvec) m in
  do! ts  <- decode_fields (Symbolic.inputs op)
                           (Concrete.ct1 mvec,
                            Concrete.ct2 mvec,
                            Concrete.ct3 mvec) m;
  Some (Symbolic.mkIVec op tpc ti ts).

Definition decode_ovec op (rvec : Concrete.RVec (word t))
                       (m : word_map t (atom (word t) (word t)))
                       : Symbolic.OVec wrapped_tag op :=
  {| Symbolic.trpc := decode (Concrete.ctrpc rvec) m;
     Symbolic.tr := match Symbolic.outputs op as o return Symbolic.type_of_result _ o with
                    | Some o => @decode _ _ (et o) (Concrete.ctr rvec) m
                    | None => tt
                    end |}.

(* Just for clarity *)
Let TCopy : word t := TNone.

Definition ground_rules : Concrete.rules (word t) :=
  let mk op := Concrete.mkMVec (op_to_word op) TKernel TKernel
                               TNone TNone TNone in
  [
   (mk NOP, Concrete.mkRVec TCopy TNone);
   (mk CONST, Concrete.mkRVec TCopy TKernel);
   (mk MOV, Concrete.mkRVec TCopy TCopy);
   (mk (BINOP ADD), Concrete.mkRVec TCopy TKernel);
   (mk (BINOP SUB), Concrete.mkRVec TCopy TKernel);
   (mk (BINOP MUL), Concrete.mkRVec TCopy TKernel);
   (mk (BINOP EQ),  Concrete.mkRVec TCopy TKernel);
   (mk (BINOP LEQ),  Concrete.mkRVec TCopy TKernel);
   (mk (BINOP AND),  Concrete.mkRVec TCopy TKernel);
   (mk (BINOP OR),  Concrete.mkRVec TCopy TKernel);
   (mk (BINOP SHRU),  Concrete.mkRVec TCopy TKernel);
   (mk (BINOP SHL),  Concrete.mkRVec TCopy TKernel);
   (mk LOAD, Concrete.mkRVec TCopy TCopy);
   (mk STORE, Concrete.mkRVec TCopy TCopy);
   (mk JUMP, Concrete.mkRVec TCopy TNone);
   (mk BNZ, Concrete.mkRVec TCopy TNone);
   (mk JAL, Concrete.mkRVec TCopy TCopy);
   (mk JUMPEPC, Concrete.mkRVec TCopy TNone);
   (mk ADDRULE, Concrete.mkRVec TCopy TNone);
   (mk GETTAG, Concrete.mkRVec TCopy TKernel);
   (mk PUTTAG, Concrete.mkRVec TCopy TNone)
  ].

Definition ivec_of_uivec (ivec : Symbolic.IVec tty) : Symbolic.IVec wrapped_tag :=
  match ivec with
  | Symbolic.mkIVec op tpc ti ts =>
    match op with
      | SERVICE =>
        Symbolic.mkIVec NOP (USER tpc) (ENTRY ti) tt
      | _ =>
        Symbolic.mkIVec op (USER tpc) (USER ti) (hmap (fun tk tg => (USER tg)) ts)
    end
  end.

Fixpoint ensure_all_user (ks : list Symbolic.tag_kind) : hlist wrapped_tag ks -> option (hlist tty ks) :=
  match ks with
  | []      => fun _  => Some tt
  | k :: ks => fun ts => match fst ts, ensure_all_user (snd ts) with
                         | USER t, Some ts => Some (t, ts)
                         | _, _ => None
                         end
  end.

Definition uivec_of_ivec (ivec : Symbolic.IVec wrapped_tag) : option (Symbolic.IVec tty) :=
  match ivec with
  | Symbolic.mkIVec op (USER tpc) ti ts =>
    match op, ti with
    | NOP, ENTRY ti => Some (Symbolic.mkIVec SERVICE tpc ti tt)
    | _, USER ti    => omap (Symbolic.mkIVec op tpc ti) (ensure_all_user ts)
    | _, _          => None
    end
  | _ => None
  end.

Lemma ivec_of_uivecK : pcancel ivec_of_uivec uivec_of_ivec.
Proof.
  move => [op tpc ti ts] /=.
  case: op ts => *;
  by repeat match goal with
  | t : hlist _ _ |- _ => simpl in t
  | t : unit |- _ => destruct t
  | t : prod _ _ |- _ => destruct t
  end.
Qed.

Lemma ivec_of_uivec_inj : injective ivec_of_uivec.
Proof. exact: pcan_inj ivec_of_uivecK. Qed.

Lemma ivec_of_uivec_privileged :
  forall ivec,
    privileged_op (Symbolic.op (ivec_of_uivec ivec)) =
    privileged_op (Symbolic.op ivec).
Proof.
  move => [op tpc ti ts] /=.
  by case: op ts => * /=.
Qed.

Definition decode_uivec (mvec : Concrete.MVec (word t))
                        (m : word_map t (atom (word t) (word t)))
                        : option (Symbolic.IVec tty) :=
  do! ivec <- decode_ivec mvec m;
  uivec_of_ivec ivec.

Definition ovec_of_uovec op (uovec : Symbolic.OVec tty op) : Symbolic.OVec wrapped_tag op :=
  {| Symbolic.trpc := USER (Symbolic.trpc uovec);
     Symbolic.tr   := match Symbolic.outputs op
                      as os
                      return Symbolic.type_of_result tty os -> Symbolic.type_of_result wrapped_tag os
                      with
                      | Some tk => fun tr => USER tr
                      | None => fun _ => tt
                      end (Symbolic.tr uovec) |}.

Definition uovec_of_ovec op (ovec : Symbolic.OVec wrapped_tag op) :=
  do! trpc <- match Symbolic.trpc ovec with
              | USER trpc => Some trpc
              | _ => None
              end;
  do! tr <- match Symbolic.outputs op as o
                                      return Symbolic.type_of_result wrapped_tag o ->
                                             option (Symbolic.type_of_result tty o) with
            | Some o => fun t => match t with
                                 | USER t => Some t
                                 | _ => None
                                 end
            | None => fun t => Some tt
            end (Symbolic.tr ovec);
  Some {| Symbolic.trpc := trpc; Symbolic.tr := tr |}.

Definition decode_uovec op (rvec : Concrete.RVec (word t))
                        (m : word_map t (atom (word t) (word t)))
                        : option (Symbolic.OVec tty op) :=
  uovec_of_ovec (decode_ovec op rvec m).

End tag_encoding.
