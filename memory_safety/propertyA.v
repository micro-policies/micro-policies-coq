From mathcomp Require Import
  ssreflect ssrfun ssrbool ssrnat seq eqtype fintype path fingraph.
From extructures Require Import ord fset fmap fperm.
From CoqUtils Require Import word nominal.

Require Import lib.utils lib.fmap_utils common.types.
Require Import memory_safety.property memory_safety.abstract.
Require Import memory_safety.classes memory_safety.executable.

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
Local Notation astepf := (AbstractE.step ops sr addrs).

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
  rewrite (get_free _ hm').
  by have [eq_b''|neq_b''] := altP (b'' =P ptr.1).
by apply/hbs => {get_pc'}; eapply ReachBaseReg; eauto.
Qed.

Lemma rename_valueE pm v :
  rename pm v = match v with
                | VData w => VData w
                | VPtr ptr => VPtr (rename pm ptr.1, ptr.2)
                end.
Proof. by case: v. Qed.

Lemma rename_dataE pm (w : mword mt) :
  rename pm (VData w) = VData w.
Proof. by []. Qed.

Lemma rename_ptrE pm (ptr : pointer) :
  rename pm (VPtr ptr) = VPtr (pm ptr.1, ptr.2).
Proof. by []. Qed.

Lemma rename_stateE pm s :
  rename pm s = State (rename pm (mem s))
                      (rename pm (regs s))
                      (rename pm (pc s)).
Proof. by case: s. Qed.

Lemma renamewE k pm (w : word k) : rename pm w = w.
Proof. by []. Qed.

Local Open Scope fperm_scope.

Lemma rename_getv pm m ptr :
  getv (rename pm m) ptr =
  rename pm (getv m (rename pm^-1 ptr)).
Proof.
rewrite /getv !renamemE fst_eqvar /= !renameoE.
case e: (m (rename _ _)) => [fr|] //=.
rewrite [in RHS]fun_if /= !renamewE size_map.
case: ifP=> // in_bounds.
by rewrite (nth_map (VData 0%w) _ _ in_bounds).
Qed.

Lemma rename_updv pm m m' ptr v :
  updv m ptr v = Some m' ->
  updv (rename pm m) (rename pm ptr) (rename pm v) =
  Some (rename pm m').
Proof.
rewrite /updv -[(rename pm ptr).1]fst_eqvar -[(rename pm m) _]getm_eqvar.
case m_ptr: (m ptr.1)=> [fr|] //=.
rewrite renamewE size_map.
case: ifP=> //= h_off [<-].
by rewrite setm_eqvar [in RHS]renamesE map_cat /= map_take map_drop.
Qed.

Lemma rename_updr pm rs rs' r v :
  updm rs r v = Some rs' ->
  updm (rename pm rs) r (rename pm v) = Some (rename pm rs').
Proof.
rewrite /updm renamemE renamewE.
case rs_r: (rs r) => [v'|] //= [<-{rs'}].
by rewrite setm_eqvar renamewE.
Qed.

Global Instance lift_binop_eqvar f : {eqvar (@lift_binop mt f)}.
Proof.
case: f=> [] pm [w1|[p1 o1]] _ <- [w2|[p2 o2]] _ <- //=;
rewrite ?renamewE ?(can_eq (renameK pm));
try match goal with
| p1 : name, p2 : name |- context [?p1 == ?p2] =>
  case: (altP (p1 =P p2)) => ? //; subst
end;
solve [move=> [<-]; rewrite rename_valueE //=].
Qed.

Lemma rename_lift_binop pm f v1 v2 v3 :
  lift_binop f v1 v2 = Some v3 ->
  lift_binop f (rename pm v1) (rename pm v2) = Some (rename pm v3).
Proof. by move=> h; rewrite -[LHS]lift_binop_eqvar; rewrite h. Qed.

(* Redeclaring instances to make type-class inference work *)
Canonical memory_nominalType := Eval hnf in [nominalType of memory mt].
Canonical frame_nominalType := Eval hnf in [nominalType of frame mt].

Lemma free_fun_eqvar : {eqvar @free_fun mt}.
Proof. by rewrite /free_fun /=; finsupp. Qed.

Lemma rename_free pm m m' b :
  free_fun m b = Some m' ->
  free_fun (rename pm m) (pm b) = Some (rename pm m').
Proof. by move=> h; rewrite -renamenE -[LHS]free_fun_eqvar h. Qed.
Hint Resolve rename_free : rename_step_db.

Ltac rename_getv :=
  match goal with
  | pm : {fperm name},
    get : getv ?m ?ptr = Some ?v |- _ =>
    match m with
    | rename pm ?m' => fail 1
    | _ => idtac
    end;
    match goal with
    | _ : getv (rename pm m) (rename pm ptr) = _ |- _ => fail 1
    | |- _ => idtac
    end;
    let aget := fresh "aget" in
    first [
        have aget: getv (rename pm m) (rename pm ptr) = Some (rename pm v);
        [ by rewrite rename_getv renameK get
        | rewrite ?rename_dataE ?rename_ptrE in aget ]
      | failwith "rename_getv" ]
  end.

Ltac rename_updv :=
  match goal with
  | pm : {fperm name},
    upd : updv ?m ?ptr ?v = Some ?m' |- _ =>
    match m with
    | rename pm ?m'' => fail 1
    | _ => idtac
    end;
    match goal with
    | _ : updv (rename pm m) (rename pm ptr) _ = _ |- _ => fail 1
    | |- _ => idtac
    end;
    let aupdm := fresh "aupdm" in
    first [
        have aupdm := rename_updv pm upd;
        rewrite ?rename_dataE ?rename_ptrE in aupdm
      | failwith "rename_updv" ]
  end.

Ltac rename_getr :=
  match goal with
  | pm : {fperm name},
    get : getm ?rs ?r = Some ?v |- _ =>
    match rs with
    | rename pm ?rs' => fail 1
    | _ => idtac
    end;
    match goal with
    | _ : getm (rename pm rs) r = _ |- _ => fail 1
    | |- _ => idtac
    end;
    let agetr := fresh "agetr" in
    first [
        have agetr: getm (rename pm rs) r = Some (rename pm v);
        [ by rewrite renamemE renameK get
        | rewrite ?rename_dataE ?rename_ptrE in agetr ]
      | failwith "rename_getr" ]
  end.

Ltac rename_updr :=
  match goal with
  | pm : {fperm name},
    upd : updm ?rs ?r ?v = Some ?rs' |- _ =>
    match rs with
    | rename pm ?rs'' => fail 1
    | _ => idtac
    end;
    match goal with
    | _ : updm (rename pm rs) r _ = _ |- _ => fail 1
    | |- _ => idtac
    end;
    let aupdr := fresh "aupdr" in
    first [
        have aupdr := rename_updr pm upd;
        rewrite ?rename_dataE ?rename_ptrE in aupdr
      | failwith "rename_updr" ]
  end.

Ltac rename_lift_binop :=
  match goal with
  | pm : {fperm name},
    bo : lift_binop ?f ?v1 ?v2 = Some ?v3 |- _ =>
    match v1 with
    | rename pm _ => fail 1
    | _ => idtac
    end;
    match goal with
    | _ : lift_binop f (rename pm v1) (rename pm v2) = _ |- _ => fail 1
    | |- _ => idtac
    end;
    let abinop := fresh "abinop" in
    first [
        have abinop := rename_lift_binop pm bo;
        rewrite ?rename_dataE ?rename_ptrE in abinop
      | failwith "rename_lift_binop" ]
  end.

Ltac apply_rename_everywhere :=
  first [ rename_getv | rename_updv | rename_getr | rename_updr
        | rename_lift_binop ].

Ltac solve_rename_step_simpl :=
  solve [ eauto
        | eauto; simpl; eauto with rename_step_db
        | eauto; try rewrite !(can_eq (renameK _)); eauto ].

Ltac rename_step_simple pm :=
  intros; exists pm; rewrite !rename_stateE /=;
  repeat apply_rename_everywhere;
  rewrite ?rename_dataE /=;
  s_econstructor solve_rename_step_simpl.

Lemma rename_step s s' pm :
  step s s' ->
  exists pm', step (rename pm s) (rename pm' s').
Proof.
case: s s' /; try rename_step_simple pm.
- (* Bnz *)
  move=> m rs p *; exists pm; rewrite !rename_stateE /=.
  repeat apply_rename_everywhere.
  rewrite !rename_ptrE /=.
  (* No idea why unification can't solve this... *)
  by eapply (@step_bnz _ _ _ _ _ _ (pm p.1, p.2)); eauto.
- (* Malloc *)
  move=> m m' rs rs' sz b pc' rs_arg.
  set s := State _ _ _; set s' := rename pm s; set bs := blocks s.
  pose b' := fresh (blocks s').
  pose bs' := supp pm :|: blocks s :|: blocks s'.
  pose b'' := fresh bs'.
  pose pm' := fperm2 b' b'' * pm * fperm2 b b''.
  rewrite /malloc_fun=> - [? ?]; subst b m'.
  have pm'_s' : s' = rename pm' s.
    apply/eq_in_rename=> x x_in; rewrite /pm' fpermM /= fpermM /=.
    rewrite (@fperm2D _ _ _ x); first last.
    + apply: contraTN x_in=> /eqP -> {x}; rewrite /b''.
      apply: contra (freshP bs'); rewrite /bs'=> h; rewrite 2!in_fsetU -orbA.
      by apply/or3P/Or32.
    + apply: contraTN x_in=> /eqP -> {x}; exact/freshP.
    rewrite fperm2D //.
      rewrite /b' /s' /blocks names_rename.
      by apply/eqP=> e; move: (freshP (pm @: names s)); rewrite -e mem_imfset.
    rewrite /b''; apply/eqP=> e; move: (freshP bs'); rewrite -e /bs'.
    by rewrite in_fsetU !negb_or /s' /blocks names_rename mem_imfset // andbF.
  have pm'_b': pm' (fresh bs) = b'.
    rewrite /pm' fpermM /= fperm2L fpermM /= (_ : pm b'' = b'') ?fperm2R.
      done.
    apply/suppPn/negP=> b''_in; move: (freshP bs').
    by rewrite /bs' 2!in_fsetU !negb_or b''_in.
  move=> h1 h2.
  exists pm'; rewrite pm'_s'; eapply step_malloc; eauto.
  + by rewrite /s /= renamemE renamewE rs_arg /= renameoE /= rename_valueE.
  + rewrite /s /= /malloc_fun.
    rewrite /b' pm'_s' /s /= in pm'_b'; rewrite -pm'_b' -renamenE.
    rewrite setm_eqvar renamesE (eq_in_map _ id _).1 1?map_id; first by eauto.
    by move=> x /nseqP [-> _].
  + exact: (rename_updr _ h1).
  by rewrite /s /= renamemE renamewE h2.
Qed.

Lemma names_state s :
  names s = names (mem s) :|: names (regs s) :|: names (pc s).
Proof. by []. Qed.

Lemma getv_union m m' p v :
  fdisjoint (names m) (domm m') ->
  getv m p = Some v ->
  getv (unionm m' m) p = Some v.
Proof.
move=> /(fdisjointP _ _)/(_ p.1) hdis; rewrite /getv unionmE.
case e: (m p.1)=> [fr|] //=; case: ifP=> inb // [<-].
have hin: p.1 \in names m.
  by apply/namesmP/(@PMFreeNamesKey _ _ _ _ p.1 fr)=> //; apply/namesnP.
by rewrite -mem_domm (negbTE (hdis hin)) inb.
Qed.
Hint Resolve getv_union : separation.

Lemma getv_union' m m' p :
  fdisjoint (names m) (domm m') ->
  p.1 \notin domm m' ->
  getv (unionm m' m) p = getv m p.
Proof.
by rewrite /getv !unionmE; move=> dis1 /dommPn -> /=.
Qed.

Lemma updv_union m m' m'' p v :
  fdisjoint (names m) (domm m') ->
  updv m p v = Some m'' ->
  updv (unionm m' m) p v = Some (unionm m' m'').
Proof.
move=> /(fdisjointP _ _)/(_ p.1) hdis; rewrite /updv unionmE.
case e: (m p.1)=> [fr|] //=; case: ifP=> inb // [<-].
have hin: p.1 \in names m.
  by apply/namesmP/(@PMFreeNamesKey _ _ _ _ p.1 fr)=> //; apply/namesnP.
rewrite -mem_domm (negbTE (hdis hin)) inb; congr some; apply/eq_fmap=> b.
rewrite !(setmE, unionmE); have [-> {b}|//] := altP (b =P _).
by rewrite -mem_domm (negbTE (hdis hin)).
Qed.
Hint Resolve updv_union : separation.

Lemma updv_union' m m' p v :
  fdisjoint (names m) (domm m') ->
  p.1 \notin domm m' ->
  updv (unionm m' m) p v =
  if updv m p v is Some m'' then Some (unionm m' m'')
  else None.
Proof.
rewrite /updv unionmE => dis p_m' /=.
rewrite (dommPn _ _  p_m'); case: getm => [fr|] //=.
case: ifP=> //= _; congr Some; apply/eq_fmap=> b.
rewrite !(setmE, unionmE).
have [-> {b}|//] := altP (b =P p.1).
by rewrite (dommPn _ _ p_m').
Qed.

Lemma free_union' m m' rs r p :
  fdisjoint (names m) (domm m') ->
  fdisjoint (names rs) (domm m') ->
  rs r = Some (VPtr p) ->
  free_fun (unionm m' m) p.1 =
  if free_fun m p.1 is Some m'' then Some (unionm m' m'')
  else None.
Proof.
rewrite /free_fun !unionmE => dis1 dis2 get_r.
have m'_p : p.1 \notin domm m'.
  move/fdisjointP: dis2; apply.
  apply/namesmP/@PMFreeNamesVal; try eassumption.
  by rewrite names_valueE in_fset1.
rewrite (dommPn _ _ m'_p) /=; case: (m p.1)=> [fr|] //=.
congr Some; apply/eq_fmap=> b.
rewrite !(remmE, unionmE); have [-> {b}|//] := altP (b =P _).
by rewrite (dommPn _ _ m'_p) /=.
Qed.

Lemma free_union m m' m'' b :
  fdisjoint (names m) (domm m') ->
  free_fun m b = Some m'' ->
  free_fun (unionm m' m) b = Some (unionm m' m'').
Proof.
move=> /(fdisjointP _ _)/(_ b) hdis; rewrite /free_fun unionmE.
case e: (m b)=> [fr|] //= [<-].
have hin: b \in names m.
  by apply/namesmP/(@PMFreeNamesKey _ _ _ _ b fr)=> //; apply/namesnP.
rewrite -mem_domm (negbTE (hdis hin)); congr some; apply/eq_fmap=> b'.
rewrite !(remmE, unionmE); have [-> {b'}|//] := altP (b' =P _).
by rewrite -mem_domm (negbTE (hdis hin)).
Qed.
Hint Resolve free_union : separation.

Definition add_mem m s :=
  State (unionm m (mem s)) (regs s) (pc s).

Lemma get_reg_disjoint rs r v bs :
  fdisjoint (names rs) bs ->
  rs r = Some v ->
  fdisjoint (names v) bs.
Proof.
move=> dis_rs get_rs; apply: fdisjoint_trans; try eassumption.
apply/fsubsetP=> /= n n_in; apply/namesmP.
by apply: PMFreeNamesVal; eauto.
Qed.

Lemma get_mem_disjoint m x v bs :
  fdisjoint (names m) bs ->
  getv m x = Some v ->
  fdisjoint (names v) bs.
Proof.
rewrite /getv; case e: getm=> [fr|] //=.
case: ifP=> // x_fr dis [<-].
have {dis} dis : fdisjoint (names fr) bs.
  apply: fdisjoint_trans; try eassumption.
  apply/fsubsetP=> /= n n_in; apply/namesmP.
  by apply: PMFreeNamesVal; eauto.
apply: fdisjoint_trans; try eassumption.
by eapply nom_finsuppP; finsupp.
Qed.

Lemma lift_binop_disjoint f v1 v2 v3 bs :
  lift_binop f v1 v2 = Some v3 ->
  fdisjoint (names v1) bs ->
  fdisjoint (names v2) bs ->
  fdisjoint (names v3) bs.
Proof.
move=> op dis1 dis2.
suffices h: fsubset (names (Some v3)) (names v1 :|: names v2).
  by apply: (fdisjoint_trans h); rewrite fdisjointUl dis1.
by rewrite -op; eapply nom_finsuppP; finsupp.
Qed.

(* FIXME: These declarations shouldn't be needed *)
Canonical registers_nominalType := Eval hnf in [nominalType of registers mt].
Canonical reg_nominalType := Eval hnf in [nominalType of reg mt].

Lemma upd_reg_disjoint rs rs' r bs v :
  updm rs r v = Some rs' ->
  fdisjoint (names rs) bs ->
  fdisjoint (names v) bs ->
  fdisjoint (names rs') bs.
Proof.
move=> h; rewrite (updm_set h) {h rs'} => dis_rs dis_v.
suffices: fdisjoint (names rs :|: names r :|: names v) bs.
  apply: fdisjoint_trans; eapply nom_finsuppP.
  (* FIXME: finsupp used to work here, but it does not anymore... *)
  move=> s sP.
  simple eapply nomR_app.
  simple eapply nomR_app.
  simple eapply nomR_app.
  (* Weird: the typeclasses debugger claims that it is using [simple apply
     setm_eqvar] to solve this goal.  However, adding [simple] below causes the
     goal to fail.  *)
  apply setm_eqvar.
  (* finsupp. (* Does not work... *) *)
  eapply nomR_nominalJ.
  finsupp. (* Now it does work *)
  finsupp.
  by finsupp.
by rewrite 2!fdisjointUl dis_rs dis_v namesT fdisjoint0s.
Qed.

Lemma upd_mem_disjoint m m' x bs v :
  updv m x v = Some m' ->
  fdisjoint (names m) bs ->
  fdisjoint (names v) bs ->
  fdisjoint (names m') bs.
Proof.
rewrite /updv; case e: getm => [fr|] //=.
case: ifP=> // x_fr [<-] dis_m dis_v.
have dis_x : fdisjoint (names x.1) bs.
  apply: fdisjoint_trans; try exact: dis_m.
  apply/fsubsetP=> n n_x.
  apply/namesmP.
  by apply:PMFreeNamesKey; eauto.
have dis_fr : fdisjoint (names fr) bs.
  apply: fdisjoint_trans; try exact: dis_m.
  apply/fsubsetP=> /= n n_in; apply/namesmP.
  by apply: PMFreeNamesVal; eauto.
suffices: fdisjoint (names m :|: names v :|: names x :|: names fr) bs.
  apply: fdisjoint_trans.
  eapply nom_finsuppP.
  (* FIXME: finsupp cannot solve this by itself *)
  move=> ??; eapply setm_eqvar.
  eapply nomR_nominalJ. finsupp. finsupp. finsupp.
rewrite fdisjointUl dis_fr fdisjointUl namespE namesT fsetU0 dis_x.
by rewrite fdisjointUl dis_v dis_m.
Qed.

Lemma free_fun_disjoint m b m' bs :
  fdisjoint (names m) bs ->
  fdisjoint (names b) bs ->
  free_fun m b = Some m' ->
  fdisjoint (names m') bs.
Proof.
move=> dis_m dis_b e; rewrite -[names m']/(names (Some m')) -e.
have ?: fsubset (names (free_fun m b)) (names m :|: names b).
  (* FIXME: finsupp used to solve this until 8.7, but it can't now... *)
  eapply nom_finsuppP=> ??; eapply free_fun_eqvar; finsupp.
apply: fdisjoint_trans; first by eauto.
by rewrite fdisjointUl /= dis_m.
Qed.

Ltac solve_frame_ok_disjoint :=
  match goal with
  | UPD : updm ?rs ?r ?v = Some ?rs',
    DIS : is_true (fdisjoint (names ?rs) ?bs) |-
    is_true (fdisjoint (names ?rs') ?bs) =>
    apply: (upd_reg_disjoint UPD DIS)
  | DIS : is_true (fdisjoint (names ?rs) ?bs),
    GET : getm ?rs ?r = Some ?v |-
    is_true (fdisjoint (names ?v) ?bs) =>
    apply: (get_reg_disjoint DIS GET)
  | _ : lift_binop _ _ _ = Some ?v |-
    is_true (fdisjoint (names ?v) _) =>
    apply: lift_binop_disjoint; eauto
  | _ : getv _ _ = Some ?v |-
    is_true (fdisjoint (names ?v) _) =>
    apply: get_mem_disjoint; eauto
  | _ : updv _ _ _ = Some ?m' |-
    is_true (fdisjoint (names ?m') _) =>
    apply: upd_mem_disjoint; eauto
  | _ : free_fun _ _ = Some ?m |-
    is_true (fdisjoint (names ?m) _) =>
    apply: free_fun_disjoint; try eassumption
  | |- is_true (fdisjoint _ _) => exact: fdisjoint0s
  | _ => done
  end.

Ltac solve_frame_ok_simpl :=
  intros;
  match goal with
  | H : is_true [&& fdisjoint _ _, fdisjoint _ _ & fdisjoint _ _] |- _ =>
    let dism := fresh "dism" in
    let disrs := fresh "disrs" in
    let disp := fresh "disp" in
    case/and3P: H => [dism disrs disp];
    exists fperm_one; rewrite rename1; split;
    [rewrite /add_mem /=; s_econstructor solve [eauto with separation]|
     rewrite 2!fdisjointUl /= -andbA; apply/and3P;
     split; repeat solve_frame_ok_disjoint]
  end.

Lemma frame_ok m s s' :
  fdisjoint (names s) (domm m) ->
  step s s' ->
  exists pm,
    step (add_mem m s) (add_mem m (rename pm s')) /\
    fdisjoint (names (rename pm s')) (domm m).
Proof.
rewrite names_state 2!fdisjointUl -andbA.
move=> dis hstep; case: s s' / hstep dis=> /=; try solve_frame_ok_simpl.
(* Malloc *)
move=> m' m'' rs rs' sz b [bpc opc].
rewrite /blocks /add_mem /=; set s := State _ _ _; set s' := State _ _ _.
set old := names s; set new := names s'.
rewrite /malloc_fun=> get_sz [eb em''] upd get_ra; subst b m''.
case/and3P=> [dism disr disp]; exists (fperm2 (fresh old) (fresh new)).
rewrite rename_valueE /= renamenE fperm2D; first last.
- apply/eqP=> e; move: (freshP new); rewrite -e; move/negP; apply.
  by rewrite /new; apply/in_blocks; econstructor; eauto.
- apply/eqP=> e; move: (freshP old); rewrite -e; move/negP; apply.
  by rewrite /new; apply/in_blocks; econstructor; eauto.
rewrite setm_eqvar renamenE fperm2L renamesE.
rewrite (@eq_in_map _ _ _ id _).1; last by move=> x /nseqP [-> ?] //.
rewrite map_id namesNNE; first last.
- apply: contra (freshP new); move: (fresh _)=> b.
  rewrite /new /s' names_state /= => hin.
  rewrite 2!in_fsetU -orbA; apply/orP; left; apply/namesmP.
  move: (fdisjointP _ _ dism _ hin)=> nin.
  case/namesmP: hin=> [b' fr hb' /namesnP e|b' fr hb' hb].
    subst b'; apply/(@PMFreeNamesKey _ _ _ _ b fr); try by apply/namesnP.
    by rewrite unionmE -mem_domm (negbTE nin).
  have b'_in: b' \in names m'.
    by apply/namesmP/(@PMFreeNamesKey _ _ _ _ b' fr)=> //; apply/namesnP.
  apply/(@PMFreeNamesVal _ _ _ _ b' fr)=> //.
  move: (fdisjointP _ _ dism b' b'_in)=> nin'.
  by rewrite unionmE -mem_domm (negbTE nin').
- apply: contra (freshP old); move: (fresh _)=> bs.
  by rewrite /old /s names_state /= => hin; rewrite 2!in_fsetU hin.
have := (rename_updr (fperm2 (fresh old) (fresh new)) upd).
rewrite rename_valueE /= renamenE fperm2L namesNNE; first last.
- apply: contra (freshP new); move: (fresh _)=> bs.
  by rewrite /new /s' names_state /= => hin; rewrite 2!in_fsetU hin orbT.
- apply: contra (freshP old); move: (fresh _)=> bs.
  by rewrite /old /s names_state /= => hin; rewrite 2!in_fsetU hin orbT.
move=> upd'; split.
  eapply step_malloc; eauto; rewrite /malloc_fun; congr pair.
  apply/eq_fmap=> x; rewrite !(setmE, unionmE) -[blocks _]/new.
  have [->{x}|hneq //] := altP (x =P _).
  rewrite -mem_domm; suff -> : fresh new \in domm m = false by [].
  apply: contraNF (freshP new); move: (fresh _)=> b /dommP [fr Hfr].
  rewrite /new /s' names_state /= 2!in_fsetU -orbA; apply/orP; left.
  apply/namesmP/(@PMFreeNamesKey _ _ _ _ b fr); first by rewrite unionmE Hfr.
  by apply/namesnP.
rewrite rename_stateE /= (updm_set upd) !setm_eqvar renamenE fperm2L.
rewrite renameT renamesE map_nseq /= 2!rename_valueE /= renamenE fperm2L.
set pm := fperm2 _ _.
have sub_m'_m: fsubset (domm m') (names m').
  by apply: fsubsetU; apply/orP; left; rewrite namesfsnE fsubsetxx.
have dis_pm : fdisjoint (names s) (supp pm).
  rewrite names_state fdisjointC /pm /old /s /s' /=.
  apply: fdisjoint_trans.
  apply: fsubset_supp_fperm2.
  rewrite !fdisjointUl fdisjointC fdisjoints1; apply/andP; split.
    exact: freshP.
  rewrite fdisjointC fdisjoints1 fdisjoint0s andbT.
  apply: contra (freshP new); move: (fresh new); apply/fsubsetP.
  rewrite /new /s' names_state /= 2!fsetU0; apply: fsetSU.
  rewrite namesm_union_disjoint; first exact: fsubsetUr.
  rewrite fdisjointC; apply: fdisjoint_trans; eauto.
have dis_new : fdisjoint (names (fresh new)) (domm m).
  rewrite namesnE fdisjointC fdisjoints1.
  apply: contra (freshP new); move: (fresh new); apply/fsubsetP.
  rewrite /new /s' names_state /= fsetU0 namesm_union_disjoint.
    apply: fsubsetU; apply/orP; left.
    apply: fsubsetU; apply/orP; left.
    by apply: fsubsetU; apply/orP; left; rewrite namesfsnE fsubsetxx.
  rewrite fdisjointC; apply: fdisjoint_trans; eauto.
have -> : rename pm m' = m'.
  apply: renameJ.
  rewrite fdisjointC.
  apply: fdisjoint_trans; try eassumption.
  by rewrite /s names_state /= fsetU0 fsubsetUl.
have dis_rs: fdisjoint (names rs) (supp pm).
  apply: fdisjoint_trans; try eassumption.
  by rewrite /s names_state /= fsetU0 fsubsetUr.
have -> : rename pm rs = rs.
  apply: renameJ.
  by rewrite fdisjointC.
have -> : rename pm (VPtr (bpc, opc)) = VPtr (bpc, opc).
  apply: renameJ.
  rewrite fdisjointC.
  by solve_frame_ok_disjoint.
rewrite names_state /= 2!fdisjointUl -andbA; apply/and3P; split.
(* FIXME: The generalizations below should not be needed to prove the set inclusions *)
- have ?: fsubset (names (setm m' (fresh new) (nseq sz (VData 0%w))))
                  (names m' :|: names (fresh new) :|: names (@VData mt 0%w)).
    move: (fresh _) (VData _)=> ??.
    eapply nom_finsuppP=> ??; eapply setm_eqvar; finsupp.
  apply: fdisjoint_trans; first by eauto.
  by rewrite 2!fdisjointUl dism dis_new /= fdisjoint0s.
- have ?: fsubset (names (setm rs syscall_ret (@VPtr mt (fresh new, 0%w))))
                  (names rs :|: names syscall_ret :|: names (@VPtr mt (fresh new, 0%w))).
    move: syscall_ret (VPtr _) => ??.
    eapply nom_finsuppP=> ??; eapply setm_eqvar; finsupp.
  apply: fdisjoint_trans; first by eauto.
  by rewrite 2!fdisjointUl disr fdisjoint0s /= fdisjointUl fdisjoint0s dis_new.
by solve_frame_ok_disjoint.
(* Free *)
apply: (@fdisjoint_trans _ _ (names (VPtr ptr))).
  exact: fsubsetUl.
solve_frame_ok_disjoint.
(* Last *)
exact: (get_reg_disjoint disrs PTR).
Qed.

Lemma not_domm_rs rs r p m' :
  fdisjoint (names rs) (domm m') ->
  rs r = Some (VPtr p) ->
  p.1 \notin domm m'.
Proof.
move/fdisjointP=> dis get_r; apply: dis.
apply/namesmP/@PMFreeNamesVal; try eassumption.
by rewrite names_valueE in_fset1.
Qed.

Lemma not_domm_pc p m' :
  fdisjoint (names (VPtr p)) (domm m') ->
  p.1 \notin domm m'.
Proof. by rewrite names_valueE fdisjointC fdisjoints1. Qed.

Ltac solve_frame_error_step :=
  match goal with
  | e : (if ?pc == ?rhs then _ else _) = _ |- _ =>
    move: e; have [->|?] := altP (pc =P rhs); move=> e //=
  | |- context[addr _ == addr _] =>
    rewrite (inj_eq (@uniq_addr _ addrs)) //=
  | e : match ?x with _ => _ end = None |- _ => destruct x
  | e : obind _ ?x = _ |- obind _ ?y = _ =>
    match y with
    | context[x] => destruct x eqn:?; simpl in * => //
    end
  | e : context[if isSome (getm ?rs ?r) then _ else _] |- _ =>
    let E := fresh "E" in
    case E: (getm rs r) e => [?|] //= e
  | e : ?x = _ |- context[?x] => rewrite e //=
  | |- context[free_fun (unionm _ _) _] =>
    erewrite free_union'; try eassumption; simpl in *
  | |- context[getv (unionm _ _) _] =>
    erewrite getv_union'; try eassumption; simpl in *
  | |- context[updv (unionm _ _) _ _] =>
    erewrite updv_union'; try eassumption; simpl in *
  | dis : is_true (fdisjoint (names ?rs) (domm ?m')),
    get_r : getm ?rs _ = Some (VPtr ?p) |-
    is_true (?p.1 \notin domm ?m') =>
    apply: not_domm_rs dis get_r
  | dis : is_true (fdisjoint (names (VPtr ?p)) (domm ?m')) |-
    is_true (?p.1 \notin domm ?m') =>
    exact: not_domm_pc dis
  | |- _ => single_match_inv; subst=> //
  end.

Ltac solve_frame_error :=
  unfold updm in *; repeat solve_frame_error_step.

Lemma frame_error m s :
  fdisjoint (names s) (domm m) ->
  astepf s = None ->
  astepf (add_mem m s) = None.
Proof.
case: s m => m rs pc m'.
rewrite names_state /= 2!fdisjointUl -andbA /AbstractE.step /add_mem.
by case/and3P=> dis_m dis_rs dis_pc *; solve_frame_error.
Qed.

Lemma noninterference s pm m1 m2 n :
  fdisjoint (names s) (domm m1) ->
  fdisjoint (names (rename pm s)) (domm m2) ->
  match stepn astepf n (add_mem m1 s),
        stepn astepf n (add_mem m2 (rename pm s)) with
  | Some s1, Some s2 =>
    exists pm' s',
      [/\ s1 = add_mem m1 s',
          fdisjoint (names s') (domm m1),
          s2 = add_mem m2 (rename pm' s') &
          fdisjoint (names (rename pm' s')) (domm m2)]
  | None, None => True
  | _, _ => False
  end.
Proof.
elim: n pm s => [|n IH] pm s.
  by move=> ?? /=; exists pm, s; split.
move=> dis1 dis2; rewrite (lock astepf) /= -lock.
case step0: (astepf s)=> [s'|].
  move/AbstractE.stepP in step0.
  have [pm1 [/AbstractE.stepP step1 dis1']] := frame_ok dis1 step0.
  have [pm' step2] := rename_step pm step0.
  have [pm2 [/AbstractE.stepP step2' dis2']] := frame_ok dis2 step2.
  rewrite step1 step2'.
  move/(_ (pm2 * pm' * pm1^-1) _ dis1'): IH.
  rewrite renameD fperm_mulsKV -renameD.
  by move/(_ dis2').
rewrite frame_error //.
case step0': (astepf (rename pm s))=> [s'|].
  move/AbstractE.stepP in step0'.
  have [pm' {step0'} /AbstractE.stepP] := rename_step pm^-1 step0'.
  by rewrite renameK step0.
by rewrite frame_error.
Qed.

End MemorySafety.
