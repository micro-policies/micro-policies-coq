Require Import ZArith List Bool.

Require Import ssreflect ssrbool eqtype ssrnat seq.

Set Implicit Arguments.
Unset Strict Implicit.

Import ListNotations.

Require Import lib.utils.
Require Import common.types.
Require Import concrete.concrete.
Require Import symbolic.rules.
Require Import symbolic.fault_handler.
Require Import symbolic.refinement_common.


Definition forallbi {A : Type} (f : nat -> A -> bool)
           (n : nat) (l : list A) : bool :=
  let fix aux (n : nat) (l : list A) : bool :=
      match l with
        | nil => true
        | a::l => f n a && aux (S n) l
      end
  in aux n l.


Lemma forallbi_app :
  forall {A} (xs ys: seq A) n f,
    forallbi f n (xs ++ ys) =
    forallbi f n xs && (forallbi f (n + (size xs)) ys).
Proof.
  move=> A.
  elim=> [| x xs IHxs] ys n f.
  * by rewrite addn0.
  * by rewrite /= IHxs addSnnS andbA.
Qed.

Lemma split_app :
  forall {A} (l : seq A) n,
    n <= size l ->
    exists l1 l2, length l1 = n /\ l1 ++ l2 = l.
Proof.
  move => A.
  elim=> [| x xs IHl] => /= n H_leq.
  * exists [] => /=. exists [].
    rewrite leqn0 in H_leq. by move/eqP: H_leq.
  * case: (IHl (n.-1)).
    by rewrite -subn1 leq_subLR add1n.
    + move => l1 [l2 [H_len H_app]].
    + case : n H_len H_leq=> [| n] H_len H_leq.
      - exists []. exists (x :: xs). by split.
      - exists (x::l1). exists l2; split => /=.
        by rewrite H_len.
        by rewrite H_app.
Qed.

Lemma rcons_length:
  forall {A} (x : A) (xs: seq A) , length xs < length (rcons xs x).
Proof.
  move => A x xs.
  rewrite -cats1 app_length [x in x < _]plus_n_O.
  apply/ltP. apply : plus_lt_compat_l => //=.
Qed.

Lemma reflect_to_ssrreflect: forall (P : Prop) (b : bool),
                        Bool.reflect P b -> reflect P b.
Proof.
  move=> P. case; move/reflect_iff => H; constructor.
  * apply H => //=.
  * move/H => contra; discriminate.
Qed.

Section ExecInv.

Context (mt : machine_types)
        (ops : machine_ops mt)
        (cp : Concrete.concrete_params mt)
        (sp : Concrete.params_spec cp)
        (fhp : fault_handler_params mt)
        (reflect_eq_word :
           forall x y : word mt, Bool.reflect (x = y) (eq_word x y)).

Variable fhstart : word mt.

Theorem word_mt_eq_dec : forall (x y : word mt),
    {x = y} + {x <> y}.
Proof.
  intros x y.
  apply reflect_dec with (b := eq_word x y).
  apply reflect_eq_word.
Defined.

Definition beq_rvec (x : Concrete.rvec (word mt)) (y : Concrete.rvec (word mt)):
  bool :=
  let (ctrpc_x, ctr_x) := x in
  let (ctrpc_y, ctr_y) := y in
    (eq_word ctrpc_x ctrpc_y) && (eq_word ctr_x ctr_y).

Definition is_masked (mv : Concrete.mvec (word mt)) (masks : Concrete.Masks) :=
  match word_to_op (Concrete.cop mv) with
    | Some op =>
      let mask := masks (Concrete.is_kernel_tag ops (Concrete.ctpc mv)) op in
      let masked_mv := Concrete.mask_dc (Concrete.dc mask) mv in
        Concrete.beq_mvec ops mv masked_mv
    | None => false
  end.


Lemma eq_wordP :
  forall (x y : word mt), reflect (x = y) (x =? y)%word.
Proof.
  move => x y; apply : reflect_to_ssrreflect => //=.
Qed.

Lemma beq_mvecP :
forall mvec mvec',
  reflect (mvec = mvec') (Concrete.beq_mvec ops mvec mvec').
Proof.
  move=> mvec mvec'. apply: (@iffP ((Concrete.beq_mvec ops mvec mvec') )).
  + apply idP.
  + rewrite /Concrete.beq_mvec.
    case: mvec; case: mvec'.
    move => cop ctpc cti ct1 ct2 ct3 cop' ctpc' cti' ct1' ct2' ct3'.
    repeat (move/andP => [H /eq_wordP ->]; move: H).
    by move/eq_wordP => ->.
  + rewrite /Concrete.beq_mvec.
    case: mvec; case: mvec'.
    move => cop ctpc cti ct1 ct2 ct3 cop' ctpc' cti' ct1' ct2' ct3'.
    move => [-> -> -> -> -> ->].
    by repeat (apply/andP; split); apply/eq_wordP.
Qed.

Lemma beq_rvecP :
  forall rvec rvec',
     reflect (rvec = rvec') (beq_rvec rvec rvec').
Proof.
  move=> rvec rvec'. apply: (@iffP ((beq_rvec rvec rvec') )).
  + apply idP.
  + case: rvec; case rvec' => ctrpc ctr ctrpc' ctr'.
    by rewrite /beq_rvec => /andP [/eq_wordP -> /eq_wordP ->].
  + case: rvec; case rvec' => ctrpc ctr ctrpc' ctr'.
    move => [-> ->]. rewrite /beq_rvec.
    by apply/andP; split; apply/eq_wordP.
Qed.

Lemma masking_preserves_op:
  forall mvec mvec' op,
    word_to_op (Concrete.cop mvec) = Some op ->
    mvec' = Concrete.mask_dc
              (Concrete.dc
                 (masks (Concrete.is_kernel_tag ops (Concrete.ctpc mvec)) op))
              mvec ->
    word_to_op (Concrete.cop mvec') = Some op.
Proof.
  move=> mvec mvec' op.
  case: mvec => /= cop ctpc cti ct1 ct2 ct3 H_op.
  case: mvec' => /= cop' ctpc' cti' ct1' ct2' ct3'.
  by move => [->].
Qed.

Lemma is_maskedP :
  forall mvec,
    reflect
      (exists mvec' op,
         word_to_op (Concrete.cop mvec') = Some op /\
         mvec = Concrete.mask_dc
                  (Concrete.dc
                     (masks (Concrete.is_kernel_tag ops (Concrete.ctpc mvec'))
                            op))
                  mvec')
      (is_masked mvec masks).
Proof.
  move=> mvec. apply: (@iffP (is_masked mvec masks)) => //.
  * apply idP.
  * rewrite /is_masked.
    remember (word_to_op (Concrete.cop mvec)) as op_opt.
    case : op_opt Heqop_opt => // op H_op.
    move/beq_mvecP => H_mvec.
    by exists mvec; exists op; split.
  * rewrite /is_masked.
    move => [mvec' [op [H_op H_mvec]]].
    move : (@masking_preserves_op mvec' mvec op H_op H_mvec) => ->.
    apply/beq_mvecP. rewrite H_mvec.
    case: mvec' H_op {H_mvec} => /= cop ctpc cti ct1 ct2 ct3 H_op.
    case: op H_op => H_op /=;
    remember (Concrete.is_kernel_tag ops ctpc) as b;
    case: b Heqb => /= <- //=.
Qed.

Lemma masking_preserves_pc_tag:
  forall mvec mvec' tag op,
    (Concrete.ctpc mvec =? tag)%word ->
    mvec' = Concrete.mask_dc
              (Concrete.dc
                 (masks (Concrete.is_kernel_tag ops (Concrete.ctpc mvec)) op))
              mvec ->
    (Concrete.ctpc mvec' =? tag)%word.
Proof.
  move=> mvec mvec' tag op.
  case: mvec => /= cop ctpc cti ct1 ct2 ct3 /eq_wordP -> ->.
  by case: (Concrete.is_kernel_tag ops tag);
  case: op; apply/eq_wordP.
Qed.

(********* Rvec Correct *********)


Definition rvec_field_correct (mem : Concrete.memory _) : bool :=
  forallb (fun addr =>
             match Concrete.get_mem mem addr with
               | Some w@x => eq_word x (tag_to_word KERNEL)
               | None => false
             end) (Concrete.rvec_fields _).


Lemma rvec_field_correctP :
  forall mem,
    reflect
      (forall addr, In addr (Concrete.rvec_fields _) ->
                    exists w,
                      Concrete.get_mem mem addr = Some w@(tag_to_word KERNEL))
      (rvec_field_correct mem).
Proof.
  move => mem.
  apply/(@iffP (rvec_field_correct mem)).
  * apply/idP.
  * move/andP => [H_Mtrpc /andP [H_Mtr _]] addr [<- | [<- | //=]].
    + case: (Concrete.get_mem mem (Concrete.Mtrpc ops)) H_Mtrpc {H_Mtr}=> //=.
      case => val tag. move/eq_wordP => H_Mtrpc.
      by exists val; rewrite H_Mtrpc.
    + case: (Concrete.get_mem mem (Concrete.Mtr ops)) H_Mtr {H_Mtrpc} => //=.
      case => val tag. move/eq_wordP => H_Mtr.
      by exists val; rewrite H_Mtr.
  * move => inv. apply/andP; split.
   + have H_In : (In (Concrete.Mtrpc ops) (Concrete.rvec_fields ops))
       by simpl; left.
     move/(_ _ H_In) : inv => [w ->].
     by apply/eq_wordP.
   + have H_In : (In (Concrete.Mtr ops) (Concrete.rvec_fields ops))
        by simpl; right; left.
     move/(_ _ H_In) : inv => [w ->].
     apply/andP; split => //. by apply/eq_wordP => //=.
Qed.


(********* Instr_mem correct *********)

Definition instr_mem_correct (mem : Concrete.memory _) : bool :=
  forallbi (fun addr instr =>
             match Concrete.get_mem mem (add_word fhstart
                                                  (Z_to_word (Z.of_nat addr)))
             with
               | Some w@x => eq_word (encode_instr instr) w
                                     && eq_word x (tag_to_word KERNEL)
               | None => false
             end
           ) 0 (kernel_protection_fh mt ops cp fhp).


Lemma instr_mem_correctP:
  forall mem,
    reflect
      (forall addr instr,
         nth_error (kernel_protection_fh mt ops cp fhp) addr = Some instr ->
         Concrete.get_mem mem (add_word fhstart (Z_to_word (Z.of_nat addr))) =
         Some (encode_instr instr)@(tag_to_word KERNEL))
    (instr_mem_correct mem).
Proof.
  move=> mem. apply/(@iffP (instr_mem_correct mem)); rewrite /instr_mem_correct.
  * apply/idP.
  * remember (kernel_protection_fh mt ops cp fhp) as lst.
    move => Hbool addr instr H_nth {Heqlst}.
    move : Hbool.
    move/leP : (@nth_error_valid _ addr lst _ H_nth) (H_nth)=> H_lt {H_nth}.
    have [l1 [l2 [<- <-]]]:
      exists l1 l2, length l1 = addr /\ l1 ++ l2 = lst
      by apply : split_app; apply: ltnW.
    rewrite forallbi_app add0n.
    move =>  H_nth /andP [_ H_bool].
    case : l2 H_bool H_nth => [| x xs] //= H_bool H_nth.
    + apply nth_error_valid in H_nth. rewrite cats0 in H_nth.
      move/ltP/ltn_eqF: H_nth. rewrite eq_refl. discriminate.
    + move/andP: H_bool H_nth.
      case :
        (Concrete.get_mem mem (fhstart + Z_to_word (Z.of_nat (length l1)))%word)
         => [| [c _] //].
      case => val tag.
      rewrite nth_error_app'.
      by move => [/andP [/eq_wordP <- /eq_wordP <-]] _ [->].
  * elim/last_ind : (kernel_protection_fh mt ops cp fhp)=> [|xs x IHxs] inv //=.
    rewrite -cats1 forallbi_app IHxs /=.
    + rewrite andbC (inv _ x) /=.
      by apply/andP; split; apply/eq_wordP => //=.
      by rewrite -cats1; apply nth_error_app'.
    + move=> addr instr H.
      rewrite (inv _ instr) //= -cats1.
      by apply index_list_app.
Qed.

(********* Mvec_correct *********)

Definition mvec_correct : bool :=
  forallbi (fun addr _ =>
             if in_dec word_mt_eq_dec
                       (add_word fhstart (Z_to_word (Z.of_nat addr)))
                       (Concrete.mvec_and_rvec_fields _)
             then false
             else true
          ) 0 (kernel_protection_fh mt ops cp fhp).



Lemma mvec_correctP :
    reflect
      (forall addr, (addr < length (kernel_protection_fh mt ops cp fhp))%coq_nat ->
                    ~ In (add_word fhstart (Z_to_word (Z.of_nat addr)))
                      (Concrete.mvec_and_rvec_fields _))
      mvec_correct.
Proof.
  apply/(@iffP (mvec_correct)); rewrite /mvec_correct.
  * apply/idP.
  * remember (kernel_protection_fh mt ops cp fhp) as lst.
    move => H_bool addr /ltP H_lt {Heqlst}. move : H_bool (H_lt).
    have [l1 [l2 [<- <-]]]:
      exists l1 l2, length l1 = addr /\ l1 ++ l2 = lst
      by apply : split_app; apply : ltnW.
    case: l2 => [| x xs] H_bool {H_lt} H_lt.
    + rewrite cats0 in H_lt. move/ltn_eqF : H_lt.
      rewrite eq_refl. discriminate.
    + rewrite forallbi_app add0n in H_bool.
      move/andP: H_bool => [_ /andP [H_bool _]] //=.
      case : (in_dec word_mt_eq_dec
                  (fhstart + Z_to_word (Z.of_nat (length l1)))%word
                  (Concrete.mvec_and_rvec_fields ops)) contra H_bool => //=.
  * elim/last_ind : (kernel_protection_fh mt ops cp fhp)=> [// |xs x IHxs] inv.
    rewrite -cats1 forallbi_app add0n.
    apply/andP; split.
    + apply IHxs => addr /ltP H_lt. apply inv.
      apply/ltP/(@ltn_trans (length xs)) => //. exact : rcons_length.
    + apply/andP; split => //.
      case: (in_dec word_mt_eq_dec
          (fhstart + Z_to_word (Z.of_nat (size xs)))%word
          (Concrete.mvec_and_rvec_fields ops)) => // a.
      exfalso. apply : (inv (length xs)) => //.
      exact/ltP/rcons_length.
Qed.

 (********* Cache_correct  *********)

Definition cache_correct1 (cache : Concrete.rules (word mt)) : bool :=
  forallb
    (fun (mrvec : Concrete.rule (word mt)) =>
       let (mv, _) := mrvec in
       if is_masked mv masks && eq_word (Concrete.ctpc mv) Concrete.TKernel
       then
         match word_to_op (Concrete.cop mv) with
           | Some op =>
             match assoc_list_lookup cache (Concrete.beq_mvec ops mv) with
               | Some rv =>
                 match
                   assoc_list_lookup concrete_ground_rules
                                     (Concrete.beq_mvec ops mv)
                 with
                   | Some rv' =>
                     let (ct_trpc, ct_tr) := Concrete.ct (masks true op) in
                     match (ct_trpc, ct_tr) with
                       | (None, None) => beq_rvec rv rv'
                       | (None, _) =>
                         eq_word (Concrete.ctrpc rv) (Concrete.ctrpc rv')
                       | (_, None) =>
                         eq_word (Concrete.ctr rv) (Concrete.ctr rv')
                       | (_, _) => true
                     end
                   | None => false
                 end
               | None => true
             end
           | None => false
         end
       else true
    ) cache.



Lemma cache_lemma :
  forall mvec mvec' rvec op cache,
    Concrete.cache_lookup _ cache masks mvec = Some rvec ->
    Some op = word_to_op (Concrete.cop mvec) ->
    mvec' =
    Concrete.mask_dc
      (Concrete.dc (masks (Concrete.is_kernel_tag ops (Concrete.ctpc mvec)) op))
      mvec ->
    (exists rvec', In (mvec', rvec') cache).
Proof.
  move => mvec mvec' rvec op cache H_cache H_op H_mask.
  move : H_cache.
  rewrite /Concrete.cache_lookup -H_op /= -H_mask.
  elim: cache => [| x xs IHxs] //=.
  case x => mvec_x rvec_x.
  case : beq_mvecP.
  + by move => ->; exists rvec_x; left.
  + move : IHxs.
    case : (assoc_list_lookup xs (Concrete.beq_mvec ops mvec')) => a //=.
    move=> IHxs _ H.
    move : (IHxs H) => [rvec' H_In].
    by exists rvec'; right.
Qed.

Lemma cache_lemma' :
  forall mvec mvec' rvec' op cache,
    In (mvec', rvec') cache ->
    Some op = word_to_op (Concrete.cop mvec) ->
    mvec' =
    Concrete.mask_dc
      (Concrete.dc (masks (Concrete.is_kernel_tag ops (Concrete.ctpc mvec)) op))
      mvec ->
    exists rvec, Concrete.cache_lookup _ cache masks mvec = Some rvec.
Proof.
  move => mvec mvec' rvec' op cache.
  elim : cache => [//| x xs IHxs /=] H_In H_op H_mask.
  rewrite /Concrete.cache_lookup -H_op /= -H_mask.
  case: H_In => [-> | H_In].
  + case: beq_mvecP => //=.
    eexists; reflexivity.
  + move/(_ H_In H_op H_mask) : IHxs => [rvec H_cache].
    move : H_cache.
    rewrite /Concrete.cache_lookup -H_op /= -H_mask.
    case: (assoc_list_lookup xs (Concrete.beq_mvec ops mvec')) => //.
    case: x => mv_x rv_x.
    case : beq_mvecP => //=.
    - eexists; reflexivity.
    - by exists rvec.
Qed.

Lemma cache_correct1P :
  forall cache,
    reflect
      (forall mvec rvec,
         Concrete.ctpc mvec = Concrete.TKernel ->
         Concrete.cache_lookup _ cache masks mvec = Some rvec ->
         Concrete.cache_lookup _ concrete_ground_rules masks mvec = Some rvec)
      (cache_correct1 cache).
Proof.
 move=> cache. apply (@iffP (cache_correct1 cache)); rewrite /cache_correct1.
 * by apply/idP.
 * move => H_bool mv rv /eq_wordP H_tag.
   remember (word_to_op (Concrete.cop mv)) as op_opt.
   case : op_opt Heqop_opt => [op H_op H_cache |//=].
   + move : H_bool => /forallb_forall H_bool.
     remember
       (Concrete.mask_dc
          (Concrete.dc
             (masks (Concrete.is_kernel_tag ops (Concrete.ctpc mv)) op)) mv)
       as mv'.
     move : (cache_lemma H_cache H_op Heqmv') => [rv' H_In].
     move/(_ (mv', rv') H_In) : H_bool H_cache.
     have -> : is_masked mv' masks
       by apply/is_maskedP; exists mv; exists op => //.
     rewrite (masking_preserves_pc_tag H_tag Heqmv')
       (masking_preserves_op _ Heqmv') //.
     Opaque assoc_list_lookup masks.
     rewrite /Concrete.cache_lookup -H_op /= -Heqmv'.
     move/eq_wordP: H_tag => ->.
     case: assoc_list_lookup {rv' H_In}; case: assoc_list_lookup => //= rv1 rv2.
     move => H_bool <-.
     case: mv H_bool {H_op rv Heqmv'} => cop ctpc cti ct1 ct2 ct3.
     case: rv1 => ctrpc1 ctr1. case: rv2 => ctrpc2 ctr2 //=.
     Transparent Concrete.ct masks.
     rewrite /Concrete.is_kernel_tag  /Concrete.copy //=.
     have -> //=: (Concrete.TKernel =? Concrete.TKernel)%word
       by apply/eq_wordP.
     case: op => //=; by case : eq_wordP => //= ->.
   + rewrite /Concrete.cache_lookup.
     by move => <- //.
 * move => inv. apply forallb_forall.
   case => mv' rv' H_In.
   case : is_maskedP => //. move => [mv [op [H_op H_mask]]].
   case : eq_wordP => // H_tag'.
   rewrite (masking_preserves_op H_op H_mask). symmetry in H_op.
   move : (cache_lemma' H_In H_op H_mask) => [rv H_cache].
   have H_tag : Concrete.ctpc mv = Concrete.TKernel
     by rewrite -H_tag'; symmetry;
     apply/eq_wordP; apply : (masking_preserves_pc_tag _ H_mask) => //;
     apply/eq_wordP.
   move/(_ mv rv H_tag H_cache) : inv.
   rewrite -H_cache /Concrete.cache_lookup -H_op /= -H_mask.
   case: assoc_list_lookup; case: assoc_list_lookup => //= rv1 rv2.
   rewrite /Concrete.is_kernel_tag.
   move/eq_wordP : H_tag => -> .
   case : mv {H_op H_mask H_cache}=> cop ctpc cti ct1 ct2 ct3.
   case : rv1  => ctrpc1 ctr1. case : rv2  => ctrpc2 ctr2.
   case: op => //=; rewrite /Concrete.copy //=; move => [->];
   case: eq_wordP => //.
Qed.

Definition cache_correct2 (cache : Concrete.rules (word mt)) : bool :=
  forallb
    (fun (mrvec : Concrete.rule (word mt)) =>
       let (mv, _) := mrvec in
       if is_masked mv masks then
         match word_to_op (Concrete.cop mv) with
           | Some op =>
             match assoc_list_lookup concrete_ground_rules
                                     (Concrete.beq_mvec ops mv) with
               | Some rv =>
                 match
                   assoc_list_lookup cache
                                     (Concrete.beq_mvec ops mv)
                 with
                   | Some rv' =>
                     let (ct_trpc, ct_tr) :=
                         Concrete.ct (masks (Concrete.is_kernel_tag
                                               ops (Concrete.ctpc mv)) op)
                     in
                     match (ct_trpc, ct_tr) with
                       | (None, None) => beq_rvec rv rv'
                       | (None, _) =>
                         eq_word (Concrete.ctrpc rv) (Concrete.ctrpc rv')
                       | (_, None) =>
                         eq_word (Concrete.ctr rv) (Concrete.ctr rv')
                       | (_, _) => true
                     end
                   | None => false
                 end
               | None => true
             end
           | None => false
         end
       else true
    ) concrete_ground_rules.


Lemma cache_correct2P :
  forall cache,
    reflect
      (forall mvec rvec,
         Concrete.cache_lookup _ concrete_ground_rules masks mvec = Some rvec ->
         Concrete.cache_lookup _ cache masks mvec = Some rvec)
      (cache_correct2 cache).
Proof.
  move=> cache. apply (@iffP (cache_correct2 cache)); rewrite /cache_correct2.
  * by apply/idP.
  * move => /forallb_forall H_bool mv rv.
    remember (word_to_op (Concrete.cop mv)) as op_opt.
    rewrite /Concrete.cache_lookup. move => H_cache.
    rewrite -H_cache.
    case : op_opt Heqop_opt => [op H_op | <- //= ].
    remember
      (Concrete.mask_dc
         (Concrete.dc
            (masks (Concrete.is_kernel_tag ops (Concrete.ctpc mv)) op)) mv)
      as mv'.
    move : (cache_lemma H_cache H_op Heqmv') => [rv' H_In].
    move/(_ (mv', rv') H_In) : H_bool. move: H_cache.
    have -> : is_masked mv' masks
      by apply/is_maskedP; exists mv; exists op => //.
    have -> : Concrete.ctpc mv' = Concrete.ctpc mv
      by apply/eq_wordP; apply (@masking_preserves_pc_tag mv mv' _ op) => //;
       apply/eq_wordP.
    rewrite /Concrete.cache_lookup -H_op /= -Heqmv' (masking_preserves_op _ Heqmv') //.
    case: assoc_list_lookup; case assoc_list_lookup => //= rv1 rv2 _.
    case: mv {H_op Heqmv'} => cop ctpc cti ct1 ct2 ct3.
    case: rv1 => ctrpc1 ctr1 //=. case: rv2 => ctrpc2 ctr2 //=.
    case: (Concrete.is_kernel_tag ops ctpc) => //=;
    case: op => //=;
    rewrite /Concrete.copy /=;
    try (by case : eq_wordP => // ->);
    try (by case: andP => [[/eq_wordP -> /eq_wordP ->]| //]).
  * move => inv. apply forallb_forall.
    case => mv' rv' H_In.
    case : is_maskedP => //. move => [mv [op [H_op H_mask]]].
    rewrite (masking_preserves_op H_op H_mask).
    symmetry in H_op.
    move : (cache_lemma' H_In H_op H_mask) => [rv H_ground].
    move/(_ mv rv H_ground) : inv. move : H_ground.
    rewrite /Concrete.cache_lookup -H_op /= -H_mask.
    case: assoc_list_lookup; case assoc_list_lookup => //=.
    have -> : Concrete.ctpc mv' = Concrete.ctpc mv
      by apply/eq_wordP; apply (@masking_preserves_pc_tag mv mv' _ op) => //;
       apply/eq_wordP.
    move => rv1 rv2 <-.
    rewrite /Concrete.is_kernel_tag.
    case : mv {H_op H_mask}=> cop ctpc cti ct1 ct2 ct3.
    case : rv1 => ctrpc1 ctr1. case : rv2  => ctrpc2 ctr2.
    case : eq_wordP;
    case: op => //=; rewrite /Concrete.copy //=;
    try (by move => _ [->]; case: eq_wordP => //);
    try (by move => _ [-> ->]; apply/andP; split; apply/eq_wordP).
Qed.


(********** Regs_correct ********)

Definition regs_correct (regs : Concrete.registers _) : bool :=
  forallb (fun r =>
             eq_word (common.tag (Concrete.get_reg regs r))
                     (tag_to_word KERNEL)
          ) (kernel_regs mt fhp) .

Lemma regs_correctP :
  forall regs,
    reflect
      (forall r, In r (kernel_regs mt fhp) ->
                 common.tag (Concrete.get_reg regs r) = tag_to_word KERNEL)
      (regs_correct regs).
Proof.
  move => regs.
  apply/(@iffP (regs_correct regs)); rewrite /regs_correct.
  * apply/idP.
  * rewrite /regs_correct.
    elim : (kernel_regs mt fhp) => [| x xs IHxs] //= Hbool r [Heq | Hin].
    + move/andP : Hbool => [Hbool _]. rewrite -Heq. by apply/eq_wordP.
    + apply IHxs => //=. by move/andP : Hbool => [_ Hbool].
  * elim : (kernel_regs mt fhp) => [| x xs IHxs] //= inv.
    apply/andP; split.
    + apply/eq_wordP. by apply : inv; left.
    + apply IHxs. move=> r H_in. by apply : inv; right.
Qed.


(********* Invariant *********)

Context {s : machine_ops_spec ops}.

Definition invariant_exec (mem : Concrete.memory _)
                          (regs : Concrete.registers _)
                          (cache : Concrete.rules (word mt)) : bool :=
  [&& rvec_field_correct mem,
      instr_mem_correct mem,
      mvec_correct,
      cache_correct1 cache,
      cache_correct2 cache
    & regs_correct regs].

Lemma invariant_execP mem regs cache tag_KERNEL :
  reflect (kernel_invariant_statement
      (fault_handler_invariant mt ops cp _ _ fhstart tag_KERNEL)
       mem regs cache)
    (invariant_exec mem regs cache).
Proof.
rewrite /= /invariant_exec.
apply: (iffP and5P).
  move=> [rvec_correct instr_correct mvec_correct cache_correct1 /andP [cache_correct2 regs_correct]].
  split; first exact/rvec_field_correctP.
  split; first exact/instr_mem_correctP.
  split; first exact/mvec_correctP.
  split; first exact/cache_correct1P.
  split; first exact/cache_correct2P; exact/regs_correctP.
move=> [rvec_correct [instr_correct [mvec_correct [cache_correct1 [cache_correct2 regs_correct]]]]].
split.
+ exact/rvec_field_correctP.
+ exact/instr_mem_correctP.
+ exact/mvec_correctP.
+ exact/cache_correct1P.
by apply/andP; split; first exact/cache_correct2P; exact/regs_correctP.
Qed.

End ExecInv.
