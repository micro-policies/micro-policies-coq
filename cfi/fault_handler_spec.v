Require Import List Arith Bool.
Import ListNotations.

Require Import ZArith.
Require Import common.common.
Require Import concrete.concrete.
Require Import lib.utils.
Import DoNotation.
Import Concrete.

Section spec.

(* Here are the various kinds of tags we use.
   For the PC:
   - KERNEL : for kernel mode
   - USER   : for user mode
     * INSTR NODE id : if a jump was taken the PC is tagged with the source node id.
     * INSTR SYSCALL : if a jump to a syscall was made.
   For registers:
   - KERNEL : for data only used in the kernel
   - USER DATA  : for data only used in user mode
   For memory:
   - KERNEL           : for kernel space
   - USER             : for user space
     * INSTR NONE     : for instructions that are not sources or destinations of indirect jumps.
     * INSTR SYSCALL  : for instructions that are system calls
     * INSTR NODE id  : for instructions that are destinations and/or sources of indirect jumps.
   - ENTRY : kernel entry points are tagged with ENTRY.
*)


Definition id := nat.
Definition eq_id := beq_nat.

Inductive instr_tag : Type :=
  | NODE : id -> instr_tag
  | SYSCALL : instr_tag
  | NONE : instr_tag.

Inductive cfi_tag : Type :=
  | INSTR   : instr_tag -> cfi_tag
  | DATA    : cfi_tag.

Definition edge := (id*id)%type.
Definition cfg_type := list edge.
Definition eq_dest (x y : edge) := 
  let '(a,a') := x in
  let '(b,b') := y in
   eq_id a a' && eq_id b b'.

Variable cfg : cfg_type.

Inductive tag : Type :=
  | USER   :  cfi_tag -> tag
  | KERNEL :  tag
  | ENTRY  : tag.

Definition cfi_tag_eq (t1 t2 : cfi_tag) : bool :=
  match t1, t2 with
    | INSTR NONE, INSTR NONE => true
    | INSTR SYSCALL, INSTR SYSCALL => true
    | INSTR (NODE x), INSTR (NODE y) => eq_id x y
    | DATA, DATA => true
    | _, _ => false
  end.
(*
Lemma cfi_tag_eqP t1 t2 : reflect (t1 = t2) (cfi_tag_eq t1 t2).
Proof.
  destruct t1, t2; simpl;
  repeat ( match goal with
    | [ |- reflect (_ = _) (eq_id _ _)] =>
      remember (eq_id i i0) as eqid; destruct eqid 
    | [ |- reflect (_=_) true] =>
      constructor;
      assert (REF : reflect (i = i0) (eq_id i i0)) by (apply id_eqP);
      apply reflect_iff in REF;
      destruct REF as [? IDEQ];
      symmetry in Heqeqid; apply IDEQ in Heqeqid; subst; reflexivity
    | [ |- reflect (_=_) false] => constructor
    | [ |- ?X _ <> ?X _ ] =>
      assert (REF : reflect (i = i0) (eq_id i i0)) by (apply id_eqP);
      rewrite <- Heqeqid in REF;
      apply reflect_iff in REF; destruct REF as [ABSURD ?];
      intro CONTRA; inversion CONTRA as [EQ]; apply ABSURD in EQ; inversion EQ 
    | [ |- ?X _ <> ?Y _ ] => intro CONTRA; inversion CONTRA
    | [ |- ?X _ <> ?Y ] => intro CONTRA; inversion CONTRA
    | [ |- ?X <> ?Y _ ] => intro CONTRA; inversion CONTRA
  end); constructor; reflexivity.
Qed.*)

Definition tag_eq (t1 t2 : tag) : bool :=
  match t1, t2 with
  | USER x, USER y => cfi_tag_eq x y
  | KERNEL, KERNEL
  | ENTRY, ENTRY => true
  | _, _ => false
  end.

Lemma tag_eqP t1 t2 : reflect (t1 = t2) (tag_eq t1 t2).
Proof.
  destruct t1, t2; simpl. 

  (*remember (cfi_tag_eq c c0) as cfieq. 

  destruct (cfieq). constructor.
  assert (reflect (c = c0) (cfi_tag_eq c c0)) by (apply cfi_tag_eqP).*)
  Admitted.

Variable TNONE : tag.

Record MVec : Type := mkMVec {
  op  : opcode;
  tpc : tag;
  ti  : tag;
  t1  : tag;
  t2  : tag;
  t3  : tag
}.

Record RVec : Type := mkRVec {
  trpc : tag;
  tr   : tag
}.

(* TODO: We need a more unified and centralized notation for specifying
handlers, ground rules, masking, and copy through. *)
(*
Inductive iexp :=
| GETID (t : stag)
*)
Inductive stag :=
| TPC
| TINSTR
| T1
| T2
| T3
| SUSER_DATA.

Inductive bexp :=
| ISUSER (t : stag)
| ISINSTR (t : stag)
| ISDEST (t1 t2 : stag)
| ISDATA (t : stag)
| TRUE
| FALSE
| AND (t1 t2 : bexp)
| OR (t1 t2 : bexp)
| THEN (t1 t2 : bexp).

Infix "&&" := AND : tag_scope.
Infix "||" := OR : tag_scope.
Notation  "x ==> y" := (THEN x y) (at level 50).

Record srule := {
  allow : bexp;
  result : stag;
  pcresult : stag
}.

Definition srules := opcode -> srule. 

Definition stag_denote (st : stag) (mvec : MVec) : tag :=
  match st with
  | TPC => tpc mvec
  | TINSTR => ti mvec
  | T1 => t1 mvec
  | T2 => t2 mvec
  | T3 => t3 mvec
  | SUSER_DATA => USER DATA
  end. 

Fixpoint bexp_denote (pt : bexp) (mvec : MVec) : bool :=
  match pt with
  | ISUSER st =>
    match stag_denote st mvec with
    | USER _ => true
    | _ => false
    end
  | ISINSTR st =>
    match stag_denote st mvec with
      | USER (INSTR _) => true
      | _ => false 
    end
  | ISDEST st1 st2 =>
    match stag_denote st1 mvec with
      | USER (INSTR (NODE n)) => 
        match stag_denote st2 mvec with
            | USER (INSTR (NODE n')) => 
              existsb (fun x => eq_dest x (n,n')) cfg
            | _ => false
        end
      | USER (INSTR SYSCALL) => false (*syscalls in ground rules*)
      | _ => true
    end
  | ISDATA st =>
    match stag_denote st mvec with
      | USER DATA => true
      | _ => false
    end
  | TRUE => true
  | FALSE => false
  | AND pt1 pt2 => bexp_denote pt1 mvec && bexp_denote pt2 mvec
  | OR pt1 pt2 => bexp_denote pt1 mvec || bexp_denote pt2 mvec
  | THEN pt1 pt2 => 
    if (bexp_denote pt1 mvec) then bexp_denote pt2 mvec else true
  end.

Local Open Scope tag_scope.

Definition srule_denote (sr : srule) (mvec : MVec) : option RVec :=
  if bexp_denote (allow sr) mvec then
    Some {| trpc := stag_denote (pcresult sr) mvec; tr := stag_denote (result sr) mvec |}
  else None.

Definition handler (srs : srules) (mvec : MVec) : option RVec :=
  srule_denote (srs (op mvec)) mvec.

Definition kernel_srules (op : opcode) : srule :=
  (* Doesn't mention calls yet. Entry points are taken care of in ground rules *)
  match op with
  | NOP => {| allow := ISUSER TPC
                       && ISINSTR TINSTR
                       && ISDEST TPC TINSTR;
              result := SUSER_DATA ; pcresult := SUSER_DATA |}
  | CONST => {| allow := ISUSER TPC && ISUSER T1
                       && ISINSTR TINSTR
                       && ISDEST TPC TINSTR;
                result := SUSER_DATA; pcresult := SUSER_DATA |}
  | MOV => {| allow := ISUSER TPC
                       && ISUSER T1 && ISUSER T2
                       && ISINSTR TINSTR 
                       && ISDEST TPC TINSTR;
              result := SUSER_DATA; pcresult := SUSER_DATA |}
  | BINOP _ => {| allow := ISUSER TPC
                         && ISUSER T1 && ISUSER T2 && ISUSER T3
                         && ISINSTR TINSTR
                         && ISDEST TPC TINSTR;
                result := SUSER_DATA; pcresult := SUSER_DATA |}
  | LOAD => {| allow := ISUSER TPC
                        && ISUSER T1 && ISUSER T2 && ISUSER T3
                        && ISINSTR TINSTR
                        && ISDEST TPC TINSTR;
               result := SUSER_DATA; pcresult := SUSER_DATA|}
  | STORE => {| allow := ISUSER TPC
                         && ISUSER T1 && ISUSER T2
                         && ISDATA T3
                         && ISDEST TPC TINSTR;
                result := SUSER_DATA; pcresult := SUSER_DATA|}
  | JUMP => {| allow := ISUSER TPC
                        && ISUSER T1
                        && ISINSTR TINSTR
                        && ISDEST TPC TINSTR;
               result := SUSER_DATA; pcresult := TINSTR |}
  | BNZ => {| allow := ISUSER TPC
                       && ISUSER T1
                       && ISINSTR TINSTR 
                       && ISDEST TPC TINSTR;
              result := SUSER_DATA; pcresult := SUSER_DATA |}
  | JAL => {| allow := ISUSER TPC
                       && ISINSTR TINSTR && ISUSER T1 && ISUSER T2
                       && ISDEST TPC TINSTR;
              result := SUSER_DATA; pcresult := TINSTR |}
  | _  => {| allow := FALSE; result := SUSER_DATA; pcresult := SUSER_DATA |} (* privileged *)
  end.

Definition rule := (MVec * RVec)%type.
Definition rules := list rule.

Definition TCOPY := TNONE.

Definition ground_rules : rules :=
  [
   (mkMVec NOP KERNEL KERNEL TNONE TNONE TNONE,
      mkRVec TCOPY TNONE);
   (* Allow user code to call kernel *)
   (mkMVec NOP (USER (INSTR SYSCALL)) ENTRY TNONE TNONE TNONE,
      mkRVec KERNEL TNONE);
   (mkMVec CONST KERNEL KERNEL TNONE TNONE TNONE,
      mkRVec TCOPY KERNEL);
   (mkMVec MOV KERNEL KERNEL TNONE TNONE TNONE,
      mkRVec TCOPY TCOPY);
   (mkMVec (BINOP ADD) KERNEL KERNEL TNONE TNONE TNONE,
      mkRVec TCOPY KERNEL);
   (mkMVec (BINOP SUB) KERNEL KERNEL TNONE TNONE TNONE,
      mkRVec TCOPY KERNEL);
   (mkMVec (BINOP MUL) KERNEL KERNEL TNONE TNONE TNONE,
      mkRVec TCOPY KERNEL);
   (mkMVec (BINOP EQ) KERNEL KERNEL TNONE TNONE TNONE,
      mkRVec TCOPY KERNEL);
   (mkMVec LOAD KERNEL KERNEL TNONE TNONE TNONE,
      mkRVec TCOPY TCOPY);
   (mkMVec STORE KERNEL KERNEL TNONE TNONE TNONE,
      mkRVec TCOPY TCOPY);
   (mkMVec JUMP KERNEL KERNEL TNONE TNONE TNONE,
      mkRVec TCOPY TNONE);
   (mkMVec BNZ KERNEL KERNEL TNONE TNONE TNONE,
      mkRVec TCOPY TNONE);
   (mkMVec JAL KERNEL KERNEL TNONE TNONE TNONE,
      mkRVec TCOPY TCOPY);
   (mkMVec JUMPEPC KERNEL KERNEL TNONE TNONE TNONE,
      mkRVec TCOPY TNONE);
   (mkMVec ADDRULE KERNEL KERNEL TNONE TNONE TNONE,
      mkRVec TCOPY TNONE);
   (mkMVec GETTAG KERNEL KERNEL TNONE TNONE TNONE,
      mkRVec TCOPY KERNEL);
   (mkMVec PUTTAG KERNEL KERNEL TNONE TNONE TNONE,
      mkRVec TCOPY TNONE)
  ].

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

End spec.
