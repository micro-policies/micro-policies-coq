(* Definition of symbolic rules and tags used for monitor protection,
   along with conversion functions towards concrete integer tags. *)

From mathcomp Require Import ssreflect ssrfun ssrbool eqtype ssrnat seq.
From extructures Require Import ord fmap.
From CoqUtils Require Import hseq word.

Require Import lib.utils.
Require Import common.types concrete.concrete symbolic.symbolic.
Import DoNotation.
Import Concrete.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

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
  fun monitor opcode =>
    if monitor then
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
Context (tty : Symbolic.tag_types).

Inductive mtag :=
| User of Symbolic.mem_tag_type tty
| Entry of Symbolic.entry_tag_type tty.

Definition is_user t :=
  if t is User _ then true else false.

Definition is_entry_tag t :=
  if t is Entry _ then true else false.

Definition sum_of_mtag (t : mtag) :=
  match t with
  | User t => inl t
  | Entry t => inr t
  end.

Definition mtag_of_sum t :=
  match t with
  | inl t => User t
  | inr t => Entry t
  end.

Lemma sum_of_mtagK : cancel sum_of_mtag mtag_of_sum.
Proof. by case. Qed.

Definition mtag_eqMixin := CanEqMixin sum_of_mtagK.
Canonical mtag_eqType := Eval hnf in EqType mtag mtag_eqMixin.

Definition wtag tk : eqType :=
  if tk == Symbolic.M then [eqType of mtag]%type
  else Symbolic.tag_type tty tk.

Definition tag_of_wtag tk : wtag tk -> option (Symbolic.tag_type tty tk) :=
  match tk with
  | Symbolic.M => fun tg =>
                    match tg with
                    | User tg => Some tg
                    | Entry _ => None
                    end
  | _          => fun tg => Some tg
  end.

Definition wtag_of_tag tk : Symbolic.tag_type tty tk -> wtag tk :=
  match tk with
  | Symbolic.M => fun tg => User tg
  | _          => fun tg => tg
  end.

Lemma tag_of_wtagK tk : ocancel (@tag_of_wtag tk) (@wtag_of_tag tk).
Proof. by case: tk=> //= -[tg|tg]. Qed.

Lemma wtag_of_tagK tk : pcancel (@wtag_of_tag tk) (@tag_of_wtag tk).
Proof. by case: tk. Qed.

Class encodable := {
  decode : forall tk, {fmap mword mt -> atom (mword mt) (mword mt)} -> mword mt -> option (wtag tk);
  decode_monotonic : forall (mem : {fmap mword mt -> atom (mword mt) (mword mt)})
                            addr x y ct st ct' st' tk,
                       mem addr = Some x@ct ->
                       decode Symbolic.M mem ct = Some (User st) ->
                       decode Symbolic.M mem ct' = Some (User st') ->
                       decode tk (setm mem addr y@ct') =1 decode tk mem;
  decode_monitor_tag : forall tk m, decode tk m Concrete.TMonitor = None
}.

(* Special case where encoding doesn't depend on memory *)
Class fencodable := {
  fdecode : forall tk, mword mt -> option (wtag tk);
  fdecode_monitor_tag : forall tk, fdecode tk Concrete.TMonitor = None
}.

Global Instance encodable_of_fencodable (e : fencodable) : encodable := {
  decode tk m w := fdecode tk w;
  decode_monotonic mem add x y ct st ct' st' tk H1 H2 H4 w := erefl;
  decode_monitor_tag tk m := fdecode_monitor_tag tk
}.

End encoding.

Section tag_encoding.

Context (mt : machine_types)
        (tty : Symbolic.tag_types)
        (et : encodable mt tty).

Variable transfer : forall ivec : Symbolic.ivec tty, option (Symbolic.vovec tty (Symbolic.op ivec)).

Definition decode_fields (fs : seq Symbolic.tag_kind)
                         (m : {fmap mword mt -> atom (mword mt) (mword mt)})
                         (ts : mword mt * mword mt * mword mt)
                         : option (hseq (fun x => option (wtag tty x)) fs) :=
  match fs return option (hseq (fun x => option (wtag tty x)) fs) with
  | [::] => Some [hseq]
  | k1 :: fs' =>
    let t1 := decode k1 m (fst (fst ts)) in
    match fs' return option (hseq (fun x => option (wtag tty x)) (k1 :: fs')) with
    | [::] => Some [hseq t1]
    | k2 :: fs'' =>
      let t2 := decode k2 m (snd (fst ts)) in
      match fs'' return option (hseq (fun x => option (wtag tty x)) (k1 :: k2 :: fs'')) with
      | [::] => Some [hseq t1; t2]
      | k3 :: fs''' =>
        let t3 := decode k3 m (snd ts) in
        match fs''' return option (hseq (fun x => option (wtag tty x)) (k1 :: k2 :: k3 :: fs''')) with
        | [::] => Some [hseq t1; t2; t3]
        | _ :: _ => None
        end
      end
    end
  end.

Fixpoint ensure_no_entry (ks : seq Symbolic.tag_kind) :
                         hseq (fun x => option (wtag tty x)) ks ->
                         option (hseq (Symbolic.tag_type tty) ks) :=
  match ks return hseq (fun x => option (wtag tty x)) ks -> option (hseq (Symbolic.tag_type tty) ks) with
  | [::]    => fun _  => Some [hseq]
  | k :: ks => fun ts =>
                 match obind (@tag_of_wtag _ k) (hshead ts), ensure_no_entry (hsbehead ts) with
                 | Some t, Some ts => Some (t :: ts)%hseq
                 | _, _ => None
                 end
  end.

Lemma ensure_no_entry_inv (ks : seq Symbolic.tag_kind)
                          (l : hseq (fun x => option (wtag tty x)) ks) (l' : hseq (Symbolic.tag_type tty) ks)
                          : ensure_no_entry l = Some l' ->
                            l = hmap (fun k x => Some (wtag_of_tag x)) l'.
Proof.
elim: ks l l' => [|k ks IH] /= => [[] []|[x l] [x' l']] //=.
case: x=> [x|] //=.
move: (tag_of_wtagK x).
case: (tag_of_wtag x)=> [x''|] //= Hx''.
case E: (ensure_no_entry _) l' => [l'|] // _ [<- <-]; move/IH in E=> {IH}.
by rewrite E Hx''.
Qed.

Definition decode_ivec (m : {fmap mword mt -> atom (mword mt) (mword mt)})
                       (mvec : Concrete.mvec mt)
                       : option (Symbolic.ivec tty) :=
  let op := Concrete.cop mvec in
  match decode Symbolic.P m (Concrete.ctpc mvec) return option (Symbolic.ivec tty) with
  | Some tpc =>
    match decode Symbolic.M m (Concrete.cti mvec) with
    | Some (User ti) =>
      do! ts <- decode_fields (Symbolic.vinputs (OP op)) m
                              (Concrete.ct1 mvec,
                               Concrete.ct2 mvec,
                               Concrete.ct3 mvec);
      do! ts <- ensure_no_entry ts;
      if Symbolic.privileged_op (OP op) then None
      else Some (@Symbolic.IVec tty (OP op) tpc ti ts)
    | Some (Entry ti) =>
      match op with
      | NOP => Some (@Symbolic.IVec tty SERVICE tpc ti [hseq])
      | _ => None
      end
    | None => None
    end
  | _ => None
  end.

Definition decode_ovec op (m : {fmap mword mt -> atom (mword mt) (mword mt)})
                       (rvec : Concrete.rvec mt)
                       : option (Symbolic.vovec tty op) :=
  match op return option (Symbolic.vovec tty op) with
  | OP op =>
    do! trpc <- match decode Symbolic.P m (Concrete.ctrpc rvec) with
                | Some trpc => Some trpc
                | _ => None
                end;
    do! tr <- match Symbolic.outputs op as o
                                        return option (Symbolic.type_of_result tty o)
              with
              | Some o => obind (@tag_of_wtag _ _) (decode o m (Concrete.ctr rvec))
              | None => Some tt
              end;
    Some {| Symbolic.trpc := trpc; Symbolic.tr := tr |}

  | SERVICE =>
    if Concrete.ctrpc rvec == Concrete.TMonitor then
      Some tt
    else None
  end.

(* Just for clarity *)
Let TCopy : mword mt := TNone.

Definition ground_rules : Concrete.rules mt :=
  let mk op := Concrete.MVec op TMonitor TMonitor TNone TNone TNone in
  [fmap
   (mk NOP, Concrete.RVec TCopy TNone);
   (mk CONST, Concrete.RVec TCopy TMonitor);
   (mk MOV, Concrete.RVec TCopy TCopy);
   (mk (BINOP ADD), Concrete.RVec TCopy TMonitor);
   (mk (BINOP SUB), Concrete.RVec TCopy TMonitor);
   (mk (BINOP MUL), Concrete.RVec TCopy TMonitor);
   (mk (BINOP EQ),  Concrete.RVec TCopy TMonitor);
   (mk (BINOP LEQ),  Concrete.RVec TCopy TMonitor);
   (mk (BINOP AND),  Concrete.RVec TCopy TMonitor);
   (mk (BINOP OR),  Concrete.RVec TCopy TMonitor);
   (mk (BINOP SHRU),  Concrete.RVec TCopy TMonitor);
   (mk (BINOP SHL),  Concrete.RVec TCopy TMonitor);
   (mk LOAD, Concrete.RVec TCopy TCopy);
   (mk STORE, Concrete.RVec TCopy TCopy);
   (mk JUMP, Concrete.RVec TCopy TNone);
   (mk BNZ, Concrete.RVec TCopy TNone);
   (mk JAL, Concrete.RVec TCopy TCopy);
   (mk JUMPEPC, Concrete.RVec TCopy TNone);
   (mk ADDRULE, Concrete.RVec TCopy TNone);
   (mk GETTAG, Concrete.RVec TCopy TMonitor);
   (mk PUTTAG, Concrete.RVec TCopy TNone)
  ].

Lemma decode_ivec_inv mvec m ivec :
  decode_ivec m mvec = Some ivec ->
  match ivec with
  | Symbolic.IVec (OP op) tpc ti ts =>
    [/\ op = Concrete.cop mvec,
        ~~ Symbolic.privileged_op (Concrete.cop mvec),
        decode Symbolic.P m (Concrete.ctpc mvec) = Some tpc,
        decode Symbolic.M m (Concrete.cti mvec) = Some (User ti) &
        decode_fields _ m (Concrete.ct1 mvec, Concrete.ct2 mvec, Concrete.ct3 mvec) =
        Some (hmap (fun k tg => Some (wtag_of_tag tg)) ts) ]
  | Symbolic.IVec SERVICE tpc ti _ =>
    [/\ Concrete.cop mvec = NOP ,
        decode Symbolic.P m (Concrete.ctpc mvec) = Some tpc &
        decode Symbolic.M m (Concrete.cti mvec) = Some (Entry ti) ]
  end.
Proof.
  case: mvec ivec => [cop ctpc cti ct1 ct2 ct3] [op tpc ti ts].
  rewrite /decode_ivec (lock Symbolic.privileged_op) /=.
  case: (decode _ m ctpc) => [tpc'|] //=.
  case: (decode _ m cti) => [[ti'|ti']|] //=; last first.
    case: cop => //= E.
    move: {E} (Symbolic.ivec_eq_inv (Some_inj E)) => [E1 E2].
    move: ti ts; rewrite -{}E1 {}E2 {op tpc'} /= => ti [] /eqP E _.
    rewrite eq_Tagged /= in E; move/eqP: E=>->.
    by constructor; eauto.
  case DEC: (decode_fields _ m _) => [ts'|] //=.
  case ENSURE: (ensure_no_entry _) => [ts''|] //=.
  rewrite -lock.
  case Hpriv: (Symbolic.privileged_op cop) => //=.
  move/ensure_no_entry_inv in ENSURE. subst ts'.
  move=> E; move: (Symbolic.ivec_eq_inv (Some_inj E)) DEC => [] {E} E1 E2.
  move: Hpriv ti ts; rewrite -{}E1 {}E2 {op tpc'} => Hpriv ti ts.
  move=> /(@pair2_inj _ _ _ _ _) -> /(@pair2_inj _ _ _ _ _) -> {ti' ts''} E.
  by constructor; eauto.
Qed.

Lemma decode_ivec_monotonic (cmem : {fmap mword mt -> atom (mword mt) (mword mt)})
      addr x y ct st (ct' : mword mt) st' :
  cmem addr = Some x@ct ->
  decode Symbolic.M cmem ct = Some (User st) ->
  decode Symbolic.M cmem ct' = Some (User st') ->
  decode_ivec (setm cmem addr y@ct') =1 decode_ivec cmem.
Proof.
  move=> Hget Hdec Hdec' [cop ctpc cti ct1 ct2 ct3].
  have Hdec_eq := decode_monotonic _ _ Hget Hdec Hdec'.
  rewrite /decode_ivec /=.
  by destruct cop; simpl; rewrite !Hdec_eq.
Qed.

Lemma decode_ovec_monotonic (cmem : {fmap mword mt -> atom (mword mt) (mword mt)}) op addr x y ct st ct' st' :
  cmem addr = Some x@ct ->
  decode Symbolic.M cmem ct = Some (User st) ->
  decode Symbolic.M cmem ct' = Some (User st') ->
  decode_ovec op (setm cmem addr y@ct') =1 decode_ovec op cmem.
Proof.
  move=> Hget Hdec Hdec' [ctrpc ctr].
  have Hdec_eq := decode_monotonic _ _ Hget Hdec Hdec'.
  rewrite /decode_ovec.
  case: op=> [op|] //=.
  by destruct op; simpl; rewrite !Hdec_eq.
Qed.

End tag_encoding.
