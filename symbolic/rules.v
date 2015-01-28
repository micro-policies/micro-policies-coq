(* Definition of symbolic rules and tags used for kernel protection,
   along with conversion functions towards concrete integer tags. *)

Require Import ssreflect ssrfun ssrbool eqtype ssrnat seq.
Require Import hseq word partmap.

Require Import lib.utils.
Require Import common.types concrete.concrete symbolic.symbolic.
Import DoNotation.
Import Concrete.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

(* Type of decoded tags. [USER ut] denotes a regular user-level
tag. [ENTRY ut] is used only for items in memory, and is used to mark
monitor-service entry points. *)

Inductive tag T : Type :=
| USER (ut : T)
| ENTRY (sct : T).

Section tag.

Variable user_tag : eqType.

Open Scope nat_scope.

Definition tag_eq (u v : tag user_tag) :=
  match u, v with
    | USER ut1, USER ut2 => ut1 == ut2
    | ENTRY sct1, ENTRY sct2 => sct1 == sct2
    | _, _ => false
  end.

Lemma tag_eqP : Equality.axiom tag_eq.
Proof.
move=> [ut1|sct1] [ut2|sct2] /=;
try (by apply: (iffP idP));
apply: (iffP eqP) => [|[<-]] //;
congruence.
Qed.

Definition tag_eqMixin := EqMixin tag_eqP.
Canonical tag_eqType := Eval hnf in EqType (tag _) tag_eqMixin.

Definition is_user (t : tag user_tag) : bool :=
  match t with
  | USER _ => true
  | _ => false
  end.

Definition is_entry_tag (t : tag user_tag) : bool :=
  match t with
  | ENTRY _ => true
  | _ => false
  end.

End tag.

Arguments ENTRY {T} _.

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
      end.

Section encoding.

Context (mt : machine_types).

(* TODO: Define the operations below in terms of a concrete encoding
   for tags. *)

Class encodable (ut : Symbolic.tag_kind -> eqType) := {
  decode : forall tk, {partmap mword mt -> atom (mword mt) (mword mt)} -> mword mt -> option (tag (ut tk));
  decode_monotonic : forall (mem : {partmap mword mt -> atom (mword mt) (mword mt)})
                            addr x y ct st ct' st' tk,
                       mem addr = Some x@ct ->
                       decode Symbolic.M mem ct = Some (USER st) ->
                       decode Symbolic.M mem ct' = Some (USER st') ->
                       decode tk (setm mem addr y@ct') =1 decode tk mem;
  decode_kernel_tag : forall tk m, decode tk m Concrete.TKernel = None
}.

(* Special case where encoding doesn't depend on memory *)
Class fencodable (ut : Symbolic.tag_kind -> eqType) := {
  fdecode : forall tk, mword mt -> option (tag (ut tk));
  fdecode_kernel_tag : forall tk, fdecode tk Concrete.TKernel = None
}.

Global Instance encodable_of_fencodable ut (e : fencodable ut) : encodable ut := {
  decode tk m w := fdecode tk w;
  decode_monotonic mem add x y ct st ct' st' tk H1 H2 H4 w := erefl;
  decode_kernel_tag tk m := fdecode_kernel_tag tk
}.

End encoding.

Section tag_encoding.

Context (mt : machine_types)
        (tty : Symbolic.tag_kind -> eqType)
        (et : encodable mt tty).

Local Notation wrapped_tag := (fun tk => [eqType of tag (tty tk)]).

Variable transfer : forall ivec : Symbolic.ivec tty, option (Symbolic.vovec tty (Symbolic.op ivec)).

Definition decode_fields (fs : seq Symbolic.tag_kind)
                         (m : {partmap mword mt -> atom (mword mt) (mword mt)})
                         (ts : mword mt * mword mt * mword mt)
                         : option (hseq (fun x => option (wrapped_tag x)) fs) :=
  match fs return option (hseq (fun x => option (wrapped_tag x)) fs) with
  | [::] => Some [hseq]
  | k1 :: fs' =>
    let t1 := decode k1 m (fst (fst ts)) in
    match fs' return option (hseq (fun x => option (wrapped_tag x)) (k1 :: fs')) with
    | [::] => Some [hseq t1]
    | k2 :: fs'' =>
      let t2 := decode k2 m (snd (fst ts)) in
      match fs'' return option (hseq (fun x => option (wrapped_tag x)) (k1 :: k2 :: fs'')) with
      | [::] => Some [hseq t1; t2]
      | k3 :: fs''' =>
        let t3 := decode k3 m (snd ts) in
        match fs''' return option (hseq (fun x => option (wrapped_tag x)) (k1 :: k2 :: k3 :: fs''')) with
        | [::] => Some [hseq t1; t2; t3]
        | _ :: _ => None
        end
      end
    end
  end.

Fixpoint ensure_all_user (ks : seq Symbolic.tag_kind) :
                         hseq (fun x => option (wrapped_tag x)) ks ->
                         option (hseq tty ks) :=
  match ks with
  | [::]      => fun _  => Some [hseq]
  | k :: ks => fun ts => match hshead ts, ensure_all_user (hsbehead ts) with
                         | Some (USER t), Some ts => Some (t :: ts)%hseq
                         | _, _ => None
                         end
  end.

Lemma ensure_all_user_inv (ks : seq Symbolic.tag_kind)
                          (l : hseq (fun x => option (wrapped_tag x)) ks) (l' : hseq tty ks)
                          : ensure_all_user l = Some l' ->
                            l = hmap (fun k x => Some (USER x)) l'.
Proof.
elim: ks l l' => [|k ks IH] /= => [[] []|[x l] [x' l']] //=.
case: x=> [[x|x]|] //.
case E: (ensure_all_user _) l' => [l'|] // _ [<- <-]; move/IH in E=> {IH}.
by rewrite E.
Qed.

Definition decode_ivec (m : {partmap mword mt -> atom (mword mt) (mword mt)})
                       (mvec : Concrete.mvec mt)
                       : option (Symbolic.ivec tty) :=
  do! op  <- op_of_word (Concrete.cop mvec);
  match decode Symbolic.P m (Concrete.ctpc mvec) with
  | Some (USER tpc) =>
    match decode Symbolic.M m (Concrete.cti mvec) with
    | Some (USER ti) =>
      do! ts  <- decode_fields (Symbolic.vinputs (OP op)) m
                               (Concrete.ct1 mvec,
                                Concrete.ct2 mvec,
                                Concrete.ct3 mvec);
      do! ts <- ensure_all_user ts;
      if Symbolic.privileged_op (OP op) then None
      else Some (Symbolic.IVec (OP op) tpc ti ts)
    | Some (ENTRY ti) =>
      match op with
      | NOP => Some (Symbolic.IVec SERVICE tpc ti [hseq])
      | _ => None
      end
    | None => None
    end
  | _ => None
  end.

Definition decode_ovec op (m : {partmap mword mt -> atom (mword mt) (mword mt)})
                       (rvec : Concrete.rvec mt)
                       : option (Symbolic.vovec tty op) :=
  match op return option (Symbolic.vovec tty op) with
  | OP op =>
    do! trpc <- match decode Symbolic.P m (Concrete.ctrpc rvec) with
                | Some (USER trpc) => Some trpc
                | _ => None
                end;
    do! tr <- match Symbolic.outputs op as o
                                        return option (Symbolic.type_of_result tty o)
              with
              | Some o => match decode o m (Concrete.ctr rvec) with
                          | Some (USER t) => Some t
                          | _ => None
                          end
              | None => Some tt
              end;
    Some {| Symbolic.trpc := trpc; Symbolic.tr := tr |}

  | SERVICE =>
    if Concrete.ctrpc rvec == Concrete.TKernel then
      Some tt
    else None
  end.

(* Just for clarity *)
Let TCopy : mword mt := TNone.

Definition ground_rules : Concrete.rules mt :=
  let mk op := Concrete.MVec (word_of_op op) TKernel TKernel
                               TNone TNone TNone in
  [::
   (mk NOP, Concrete.RVec TCopy TNone);
   (mk CONST, Concrete.RVec TCopy TKernel);
   (mk MOV, Concrete.RVec TCopy TCopy);
   (mk (BINOP ADD), Concrete.RVec TCopy TKernel);
   (mk (BINOP SUB), Concrete.RVec TCopy TKernel);
   (mk (BINOP MUL), Concrete.RVec TCopy TKernel);
   (mk (BINOP EQ),  Concrete.RVec TCopy TKernel);
   (mk (BINOP LEQ),  Concrete.RVec TCopy TKernel);
   (mk (BINOP AND),  Concrete.RVec TCopy TKernel);
   (mk (BINOP OR),  Concrete.RVec TCopy TKernel);
   (mk (BINOP SHRU),  Concrete.RVec TCopy TKernel);
   (mk (BINOP SHL),  Concrete.RVec TCopy TKernel);
   (mk LOAD, Concrete.RVec TCopy TCopy);
   (mk STORE, Concrete.RVec TCopy TCopy);
   (mk JUMP, Concrete.RVec TCopy TNone);
   (mk BNZ, Concrete.RVec TCopy TNone);
   (mk JAL, Concrete.RVec TCopy TCopy);
   (mk JUMPEPC, Concrete.RVec TCopy TNone);
   (mk ADDRULE, Concrete.RVec TCopy TNone);
   (mk GETTAG, Concrete.RVec TCopy TKernel);
   (mk PUTTAG, Concrete.RVec TCopy TNone)
  ].

Lemma decode_ivec_inv mvec m ivec :
  decode_ivec m mvec = Some ivec ->
  (exists op,
    [/\ Symbolic.op ivec = OP op &
    [/\ ~~ Symbolic.privileged_op op,
        op_of_word (Concrete.cop mvec) = Some op,
        decode Symbolic.P m (Concrete.ctpc mvec) = Some (USER (Symbolic.tpc ivec)),
        decode Symbolic.M m (Concrete.cti mvec) = Some (USER (Symbolic.ti ivec)) &
        decode_fields _ m (Concrete.ct1 mvec, Concrete.ct2 mvec, Concrete.ct3 mvec) =
        Some (hmap (fun k x => Some (USER x)) (Symbolic.ts ivec)) ]]) \/
  [/\ op_of_word (Concrete.cop mvec) = Some NOP ,
      Symbolic.op ivec = SERVICE ,
      decode Symbolic.P m (Concrete.ctpc mvec) = Some (USER (Symbolic.tpc ivec)) &
      decode Symbolic.M m (Concrete.cti mvec) = Some (ENTRY (Symbolic.ti ivec)) ].
Proof.
  case: mvec ivec => [cop ctpc cti ct1 ct2 ct3] [op tpc ti ts].
  rewrite /decode_ivec (lock Symbolic.privileged_op) /=.
  case: (op_of_word cop) => [op'|] //=.
  case: (decode _ m ctpc) => [[tpc'|?]|] //=.
  case: (decode _ m cti) => [[ti'|ti']|] //=; last first.
    case: op' => //= [] [? ? ?]. subst op tpc' ti'. right.
    constructor; eauto.
  case DEC: (decode_fields _ m _) => [ts'|] //=.
  case ENSURE: (ensure_all_user _) => [ts''|] //=.
  rewrite -lock.
  case Hpriv: (Symbolic.privileged_op op') => //=.
  move/ensure_all_user_inv in ENSURE. subst ts'.
  case: op ts => [op|] //= ts.
  move=> E. move: (Symbolic.ivec_eq_inv (Some_inj E)) DEC => [] {E} [E1] E2 E3.
  subst op' tpc' ti' => /(@pair2_inj _ _ _ _ _) H. subst ts'' => ->.
  left. eexists. split; try by eauto. rewrite Hpriv. by split; constructor; eauto.
Qed.

Lemma decode_ivec_monotonic (cmem : {partmap mword mt -> atom (mword mt) (mword mt)})
      addr x y ct st (ct' : mword mt) st' :
  cmem addr = Some x@ct ->
  decode Symbolic.M cmem ct = Some (USER st) ->
  decode Symbolic.M cmem ct' = Some (USER st') ->
  decode_ivec (setm cmem addr y@ct') =1 decode_ivec cmem.
Proof.
  move=> Hget Hdec Hdec' [cop ctpc cti ct1 ct2 ct3].
  have Hdec_eq := decode_monotonic _ _ Hget Hdec Hdec'.
  rewrite /decode_ivec /=.
  case: (op_of_word cop) => [op|] //=.
  by destruct op; simpl; rewrite !Hdec_eq.
Qed.

Lemma decode_ovec_monotonic (cmem : {partmap mword mt -> atom (mword mt) (mword mt)}) op addr x y ct st ct' st' :
  cmem addr = Some x@ct ->
  decode Symbolic.M cmem ct = Some (USER st) ->
  decode Symbolic.M cmem ct' = Some (USER st') ->
  decode_ovec op (setm cmem addr y@ct') =1 decode_ovec op cmem.
Proof.
  move=> Hget Hdec Hdec' [ctrpc ctr].
  have Hdec_eq := decode_monotonic _ _ Hget Hdec Hdec'.
  rewrite /decode_ovec.
  case: op=> [op|] //=.
  by destruct op; simpl; rewrite !Hdec_eq.
Qed.

End tag_encoding.
