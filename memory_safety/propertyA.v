Require Import Ssreflect.ssreflect Ssreflect.ssrfun Ssreflect.ssrbool.
Require Import Ssreflect.ssrnat Ssreflect.seq Ssreflect.eqtype Ssreflect.fintype.

Require Import MathComp.path MathComp.fingraph.

Require Import CoqUtils.ord CoqUtils.word CoqUtils.fset CoqUtils.partmap.
Require Import CoqUtils.fperm CoqUtils.nominal.

Require Import lib.utils lib.partmap_utils common.types.
Require Import memory_safety.property memory_safety.abstract.
Require Import memory_safety.classes.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Section MemorySafety.

Local Open Scope fset_scope.

Import Abstract.

Variable mt : machine_types.
Variable ops : machine_ops mt.
Variable sr : syscall_regs mt.
Variable addrs : memory_syscall_addrs mt.

Local Notation state := (state mt).
Local Notation pointer := [eqType of pointer mt].
Local Notation value := (value mt).

Implicit Type m : memory mt.
Implicit Type rs : registers mt.
Implicit Type s : state.
Implicit Type b : name.
Implicit Type p : pointer.
Implicit Type bs : {fset name}.
Implicit Type v : value.
Implicit Type pm : {fperm name}.

Definition references m b b' :=
  [exists offs : mword mt * mword mt,
    getv m (b, offs.1) == Some (VPtr (b', offs.2))].

Inductive reachable pc rs m b : Prop :=
| ReachBasePc p of pc = VPtr p & p.1 = b
| ReachBaseReg r p of rs r = Some (VPtr p) & p.1 = b
| ReachHop b' of reachable pc rs m b' & references m b' b.
Hint Constructors reachable.

Definition reachable_blocks pc rs m bs :=
  forall b, b \in bs <-> reachable pc rs m b.

Definition live_blocks s bs :=
  reachable_blocks (pc s) (regs s) (mem s) bs.

Lemma live_blocks_blocks s bs :
  live_blocks s bs -> {subset bs <= blocks s}.
Proof.
move=> live b /live in_bs; apply/in_blocks.
elim: b / in_bs
      => [b ptr ? ?|b r ptr|b b' _ IH /existsP [[/= off off'] /eqP hget]].
- by eapply BlocksPc; eauto.
- by eapply BlocksReg; eauto.
move: hget; rewrite /getv /=.
case mem_b': (mem s b') => [fr|] //=.
have [in_bounds [hnth]|] //= := boolP (off < size fr).
have ?: VPtr (b, off') \in fr.
  by rewrite -hnth; apply mem_nth.
by eapply BlocksMem; eauto.
Qed.

(* FIXME: Right now, this doesn't say anything about memory reads. *)
CoInductive valid_step s bs s' bs' : Prop :=
| ValidNop of mem s = mem s' & {subset bs' <= bs}
| ValidWrite p v of updv (mem s) p v = Some (mem s')
                  & {subset bs' <= bs} & p.1 \in bs
| ValidAlloc b sz of malloc_fun (mem s) (blocks s) sz = (mem s', b)
                   & {subset bs' <= b |: bs}
| ValidFree b of Abstract.free_fun (Abstract.mem s) b = Some (Abstract.mem s')
               & {subset bs' <= bs} & b \in bs.

CoInductive value_ok pc rs m : value -> Prop :=
| VOkData x : value_ok pc rs m (VData x)
| VOkPtr p of reachable pc rs m p.1 : value_ok pc rs m (VPtr p).
Hint Constructors value_ok.

CoInductive valid_pc_upd (pc pc' : value) rs m : Prop :=
| ValidPcUpd of value_ok pc rs m pc'.
Hint Constructors valid_pc_upd.

CoInductive valid_reg_upd pc rs rs' m : Prop :=
| ValidRegSame of rs = rs'
| ValidRegUpd v r of updm rs r v = Some rs' & value_ok pc rs m v.
Hint Constructors valid_reg_upd.

Lemma upd_reachable pc pc' rs rs' m bs bs' :
  reachable_blocks pc rs m bs ->
  reachable_blocks pc' rs' m bs' ->
  valid_pc_upd pc pc' rs m ->
  valid_reg_upd pc rs rs' m ->
  {subset bs' <= bs}.
Proof.
move=> hbs hbs' v_pc v_rs b /hbs' reach_b; apply/hbs.
elim: b / reach_b {hbs hbs'} => [b [b' off] /= hpc' hb'|b r [b' off]/=|b b' _].
- rewrite {}hb' {b'} in hpc'.
  case: v_pc => v_pc.
  by case: pc' / v_pc hpc' => [//|[b' off'] /= ? [<- _]].
- move=> hr hb'; move: hr; rewrite {}hb' {b'}.
  case: v_rs => [-> hr|v r' upd_rs]; first by eapply ReachBaseReg; eauto.
  move: {upd_rs} (updm_set upd_rs)=> upd_rs v_ok.
  rewrite {}upd_rs {rs'} setmE.
  have [_{r}[vE]|_ hr] := altP eqP.
    by case: v / v_ok vE => // - [b' off'] /= ? [<- _].
  by eapply ReachBaseReg; eauto.
by eapply ReachHop.
Qed.

Lemma get_reg_ok pc rs r m v bs :
  rs r = Some v -> value_ok pc rs m v.
Proof.
case: v => [?|[b off get_rs]]; constructor.
by eapply ReachBaseReg; eauto.
Qed.

Lemma get_mem_ok pc rs m p v :
  value_ok pc rs m (VPtr p) ->
  getv m p = Some v ->
  value_ok pc rs m v.
Proof.
move=> p_ok; move: {1 2}(VPtr p) p_ok (erefl (VPtr p))=> v'.
case: v' / => // - [b off] b_reach [<-].
case: v => [?|[b' off' get_p]]; constructor.
eapply ReachHop; eauto; apply/existsP; exists (off,off')=> /=.
by apply/eqP.
Qed.

Lemma lift_binop_ok pc rs m o v1 v2 v3 :
  value_ok pc rs m v1 ->
  value_ok pc rs m v2 ->
  lift_binop o v1 v2 = Some v3 ->
  value_ok pc rs m v3.
Proof.
rewrite /lift_binop.
case: v1 / => [v1|[b1 off1] hb1]; case: v2 / => [v2|[b2 off2] hb2];
case: o=> //;
try match goal with
| |- context[?b1 == ?b2] =>
  have [b1_eq_b2|b1_neq_b2] // := altP (b1 =P b2)
end;
move=> [<-]; constructor; done.
Qed.

Ltac simple_intros :=
  move=> /= *;
  repeat match goal with
  | H : live_blocks ?s ?bs |- _ =>
    match goal with
    | _ : {subset bs <= blocks s} |- _ => fail 1
    | |- _ => idtac
    end;
    let live := fresh "live" in
    let sub := fresh "sub" in
    move: H => live;
    have sub := live_blocks_blocks live;
    simpl in live, sub; simpl
  end;
  apply: ValidNop; first done.

Lemma getv_upd m m' p v :
  updv m p v = Some m' ->
  forall p', getv m' p' = if p' == p then Some v else getv m p'.
Proof.
rewrite /updv/getv/= => get_p p'; move: get_p.
case get_m: (m p.1) => [fr|] //.
have [leq_size_fr [<-]|//] := boolP (p.2 < size fr)%N.
rewrite setmE -pair_eqE /=.
have [eq_p1|neq_p1 //] := altP (p'.1 =P p.1).
rewrite size_cat size_take /= size_drop leq_size_fr.
rewrite addnS -addSn addnC subnK //.
have [eq_p2|neq_p2] := altP (p'.2 =P p.2).
  by rewrite eq_p2 leq_size_fr nth_cat size_take leq_size_fr ltnn subnn.
rewrite eq_p1 get_m.
case: ifP => // leq_size_fr'.
rewrite nth_cat size_take /= leq_size_fr; move: neq_p2; rewrite -!val_eqE /=.
case: (ltngtP p'.2 p.2) => [leq_p2|leq_p2'|eq_p2 //].
  by rewrite nth_take //.
move: (leq_p2'); rewrite -{1}(addn0 p.2) -ltn_subRL => leq_subn.
by rewrite -(@prednK (p'.2 - p.2))//= -subnS nth_drop addnC subnK // subnn.
Qed.

Ltac safe_step_simple_cases :=
  simple_intros;
  first [ solve [ eapply upd_reachable; try eassumption;
                  unfold pc, regs, mem;
                  eauto using get_reg_ok, get_mem_ok, lift_binop_ok;
                  done ]
        | failwith "solve_simple_cases" ].

Lemma safe_step s bs s' bs' :
  step s s' ->
  live_blocks s bs ->
  live_blocks s' bs' ->
  valid_step s bs s' bs'.
Proof.
case: s s' / => /=; try safe_step_simple_cases.
- move=> m m' rs pc ptr i r1 r2 v _ _ get_ptr get_v upd_m /= hbs hbs'.
  eapply ValidWrite; eauto.
    move=> b' /hbs' b'_in_bs'; apply/hbs => {hbs hbs'}.
    elim: b' / b'_in_bs'
          => [b' p [<-] {p} <-|b' r p get_p <-
             |b' b'' _ IH /existsP /= [off /eqP get_b'']] /=.
    + by eapply ReachBasePc; eauto.
    + by eapply ReachBaseReg; eauto.
    move: get_b''; rewrite (getv_upd upd_m).
    have [ptr_eq [v_eq]|ptr_neq get_b''] := altP (_ =P ptr).
      by rewrite v_eq {get_ptr} in get_v; eapply ReachBaseReg; eauto.
    by eapply ReachHop; eauto; apply/existsP; exists off; apply/eqP.
  by apply/hbs; apply/(@ReachBaseReg _ _ _ ptr.1 r1 ptr); simpl; eauto.
- move=> m m' rs rs' sz b pc' _ hm' hrs' get_pc' hbs hbs'.
  have hsub := live_blocks_blocks hbs.
  have hsub' := live_blocks_blocks hbs'.
  eapply ValidAlloc; simpl; eauto=> b' /hbs' b'_in_bs' {hbs'}.
  elim: b' / b'_in_bs'
        => [b' p [<-] {p} <-|b' r p get_p <-
           |b' b'' _ IH /existsP /= [off /eqP get_b']] /=.
  + rewrite in_fsetU1; apply/orP; right; apply/hbs.
    by eapply ReachBaseReg; eauto.
  + move: get_p; rewrite (getm_upd hrs') in_fsetU1.
    have [_{r} [<-]|r_neq get_p] := altP eqP; first by rewrite eqxx.
    by apply/orP; right; apply/hbs; eapply ReachBaseReg; eauto.
  rewrite !in_fsetU1 in IH *; have [//|neq_b' /=] := eqP.
  case/orP: IH => [/eqP eq_b''|/hbs b''_in_bs].
    move: get_b'; rewrite {}eq_b'' {b''}.
    have [in_bounds|off_bounds] := boolP (off.1 < sz)%ord.
      by rewrite (malloc_get hm' in_bounds).
    rewrite -Ord.leqNgt in off_bounds.
    by rewrite (malloc_get_out_of_bounds hm' off_bounds).
  apply/hbs; eapply ReachHop; eauto; apply/existsP; exists off; apply/eqP.
  move: get_b'; rewrite /getv/=.
  have [eq_b''|neq_b''] := b'' =P b.
    rewrite {}eq_b'' {b''} in b''_in_bs *.
    by generalize (malloc_fresh hm'); move/hbs/hsub: b''_in_bs => ->.
  by rewrite (malloc_get_neq hm' neq_b'').
move=> m m' rs ptr pc' harg hm' get_pc' /= hbs hbs'.
eapply ValidFree; simpl; first by eauto.
  move=> b' /hbs' b'_in_bs'; apply/hbs.
  elim: b' / b'_in_bs'
        => [b' p [<-] {p} <-|b' r p get_p <-
           |b' b'' _ IH /existsP /= [off /eqP get_b']] /=.
  - by eapply ReachBaseReg; eauto.
  - by eapply ReachBaseReg; eauto.
  eapply ReachHop; eauto; apply/existsP; exists off; apply/eqP.
  move: get_b'; rewrite /getv/=.
  have [eq_b''|neq_b''] := altP (b'' =P ptr.1).
    by rewrite eq_b'' (free_get_fail hm').
  by rewrite (free_get hm') // eq_sym.
by apply/hbs => {get_pc'}; eapply ReachBaseReg; eauto.
Qed.

Lemma action_valueE pm v :
  action pm v = match v with
                | VData w => VData w
                | VPtr ptr => VPtr (action pm ptr.1, ptr.2)
                end.
Proof. by case: v. Qed.

Lemma action_dataE pm (w : mword mt) :
  action pm (VData w) = VData w.
Proof. by []. Qed.

Lemma action_ptrE pm (ptr : pointer) :
  action pm (VPtr ptr) = VPtr (pm ptr.1, ptr.2).
Proof. by []. Qed.

Lemma action_stateE pm s :
  action pm s = State (action pm (mem s))
                      (action pm (regs s))
                      (action pm (pc s)).
Proof. by case: s. Qed.

Lemma actionwE k pm (w : word k) : action pm w = w.
Proof. by []. Qed.

Local Open Scope fperm_scope.

Lemma action_getv pm m ptr :
  getv (action pm m) ptr =
  action pm (getv m (action pm^-1 ptr)).
Proof.
rewrite /getv !actionmE !actionpE /= !actionoE.
case e: (m (action _ _)) => [fr|] //=.
rewrite [in RHS]fun_if /= !actionwE size_map.
case: ifP=> // in_bounds.
by rewrite (nth_map (VData 0%w) _ _ in_bounds).
Qed.

Lemma action_updv pm m m' ptr v :
  updv m ptr v = Some m' ->
  updv (action pm m) (action pm ptr) (action pm v) =
  Some (action pm m').
Proof.
rewrite /updv !actionpE /= actionmE actionK.
case m_ptr: (m ptr.1)=> [fr|] //=.
rewrite actionwE size_map.
case: ifP=> //= h_off [<-].
by rewrite actionm_set [in RHS]actionsE map_cat /= map_take map_drop.
Qed.

Lemma action_updr pm rs rs' r v :
  updm rs r v = Some rs' ->
  updm (action pm rs) r (action pm v) = Some (action pm rs').
Proof.
rewrite /updm actionmE actionwE.
case rs_r: (rs r) => [v'|] //= [<-{rs'}].
by rewrite actionm_set actionwE.
Qed.

Lemma action_lift_binop pm f v1 v2 v3 :
  lift_binop f v1 v2 = Some v3 ->
  lift_binop f (action pm v1) (action pm v2) = Some (action pm v3).
Proof.
case: f v1 v2=> [] [w1|[p1 o1]] [w2|[p2 o2]] //=;
rewrite ?actionwE ?(can_eq (actionK pm));
try match goal with
| p1 : name, p2 : name |- context [?p1 == ?p2] =>
  case: (altP (p1 =P p2)) => ? //; subst
end;
solve [move=> [<-]; rewrite action_valueE //=].
Qed.

Lemma action_free pm m m' b :
  free_fun m b = Some m' ->
  free_fun (action pm m) (pm b) = Some (action pm m').
Proof.
rewrite /free_fun actionmE actionnE actionoE fpermK.
case m_b: (m b) => [fr|] //= [<- {m'}]; congr Some.
by rewrite actionm_rem.
Qed.
Hint Resolve action_free : action_step_db.

Ltac action_getv :=
  match goal with
  | pm : {fperm name},
    get : getv ?m ?ptr = Some ?v |- _ =>
    match m with
    | action pm ?m' => fail 1
    | _ => idtac
    end;
    match goal with
    | _ : getv (action pm m) (action pm ptr) = _ |- _ => fail 1
    | |- _ => idtac
    end;
    let aget := fresh "aget" in
    first [
        have aget: getv (action pm m) (action pm ptr) = Some (action pm v);
        [ by rewrite action_getv actionK get
        | rewrite ?action_dataE ?action_ptrE in aget ]
      | failwith "action_getv" ]
  end.

Ltac action_updv :=
  match goal with
  | pm : {fperm name},
    upd : updv ?m ?ptr ?v = Some ?m' |- _ =>
    match m with
    | action pm ?m'' => fail 1
    | _ => idtac
    end;
    match goal with
    | _ : updv (action pm m) (action pm ptr) _ = _ |- _ => fail 1
    | |- _ => idtac
    end;
    let aupdm := fresh "aupdm" in
    first [
        have aupdm := action_updv pm upd;
        rewrite ?action_dataE ?action_ptrE in aupdm
      | failwith "action_updv" ]
  end.

Ltac action_getr :=
  match goal with
  | pm : {fperm name},
    get : getm ?rs ?r = Some ?v |- _ =>
    match rs with
    | action pm ?rs' => fail 1
    | _ => idtac
    end;
    match goal with
    | _ : getm (action pm rs) r = _ |- _ => fail 1
    | |- _ => idtac
    end;
    let agetr := fresh "agetr" in
    first [
        have agetr: getm (action pm rs) r = Some (action pm v);
        [ by rewrite actionmE actionK get
        | rewrite ?action_dataE ?action_ptrE in agetr ]
      | failwith "action_getr" ]
  end.

Ltac action_updr :=
  match goal with
  | pm : {fperm name},
    upd : updm ?rs ?r ?v = Some ?rs' |- _ =>
    match rs with
    | action pm ?rs'' => fail 1
    | _ => idtac
    end;
    match goal with
    | _ : updm (action pm rs) r _ = _ |- _ => fail 1
    | |- _ => idtac
    end;
    let aupdr := fresh "aupdr" in
    first [
        have aupdr := action_updr pm upd;
        rewrite ?action_dataE ?action_ptrE in aupdr
      | failwith "action_updr" ]
  end.

Ltac action_lift_binop :=
  match goal with
  | pm : {fperm name},
    bo : lift_binop ?f ?v1 ?v2 = Some ?v3 |- _ =>
    match v1 with
    | action pm _ => fail 1
    | _ => idtac
    end;
    match goal with
    | _ : lift_binop f (action pm v1) (action pm v2) = _ |- _ => fail 1
    | |- _ => idtac
    end;
    let abinop := fresh "abinop" in
    first [
        have abinop := action_lift_binop pm bo;
        rewrite ?action_dataE ?action_ptrE in abinop
      | failwith "action_lift_binop" ]
  end.

Ltac apply_action_everywhere :=
  first [ action_getv | action_updv | action_getr | action_updr
        | action_lift_binop ].

Ltac solve_action_step_simpl :=
  solve [ eauto
        | eauto; simpl; eauto with action_step_db
        | eauto; try rewrite !(can_eq (actionK _)); eauto ].

Ltac action_step_simple pm :=
  intros; exists pm; rewrite !action_stateE /=;
  repeat apply_action_everywhere;
  rewrite ?action_dataE /=;
  s_econstructor solve_action_step_simpl.

Lemma action_step s s' pm :
  step s s' ->
  exists pm', step (action pm s) (action pm' s').
Proof.
case: s s' /; try action_step_simple pm.
- (* Bnz *)
  move=> m rs p *; exists pm; rewrite !action_stateE /=.
  repeat apply_action_everywhere.
  rewrite !action_ptrE /=.
  (* No idea why unification can't solve this... *)
  by eapply (@step_bnz _ _ _ _ _ _ (pm p.1, p.2)); eauto.
- (* Malloc *)
  move=> m m' rs rs' sz b pc' rs_arg; set s := State _ _ _; set bs := blocks s.
  admit.
Qed.

End MemorySafety.
