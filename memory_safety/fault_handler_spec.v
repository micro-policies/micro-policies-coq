Require Import Arith.

(* Only the unprivileged ones *)
Inductive opcode : Set :=
  | CONST
  | MOV
  | ADD (* replaces binop *)
  | SUB (* replaces binop *)
  | LOAD
  | STORE
  | JUMP
  | BNZ
  | JAL.

Definition nonce := nat.

Inductive typ : Set :=
  | I :          typ
  | P : nonce -> typ.

Inductive tag : Set :=
  | V :          typ -> tag
  | M : nonce -> typ -> tag
  | F :                 tag
  | N :                 tag. (* none *)

Record mvec : Set := mk_mvec {
  op  : opcode;
  tpc : tag;
  ti  : tag;
  t1  : tag;
  t2  : tag;
  t3  : tag
}.

Record rvec : Set := mk_rvec {
  trpc : tag;
  tr   : tag
}.

Definition bind (A B:Type) (f:A->option B) (a:option A) : option B :=
    match a with
      | None => None
      | Some a => f a 
    end.
Notation "'do' X <- A ; B" :=
  (bind _ _ (fun X => B) A)
  (at level 200, X ident, A at level 100, B at level 200).
Notation "'do' X : T <- A ; B" :=
  (bind _ _ (fun X : T => B) A)
  (at level 200, X ident, A at level 100, B at level 200).

Definition error {A} : option A := None.

(* This micro-policy doesn't use the tpc and ti tags parts of the
   mvector, nor does it use the trpc part of the rvector *)

Definition handler (mv : mvec) : option rvec :=
  let ret r := Some (mk_rvec r N) in
  match op mv with
  | CONST => ret (V I)
  | MOV => ret (t1 mv)
  | ADD =>
    match t1 mv, t2 mv with
    | V I    , V I     => ret (V I)
    | V (P n), V I
    | V I    , V (P n) => ret (V (P n))
    | _      , _       => error
    end
  | SUB =>
    match t1 mv, t2 mv with
    | V I    , V I     => ret (V I)
    | V (P n), V I
    | V I    , V (P n) => ret (V (P n))
    | V (P n), V (P m) => if beq_nat n m then ret (V I) else error
    | _      , _       => error
    end
  | LOAD =>
    match t1 mv, t2 mv with
    | V (P n), M m t => if beq_nat n m then ret (V t) else error
    | _      , _     => error
    end
  | STORE =>
    match t1 mv, t2 mv, t3 mv with
    | V (P n), V tv, M m tm => if beq_nat n m then ret (M m tv) else error
    | _      , _ , _    => error
    end
  | JUMP =>
    match t1 mv with
    | V (P n) => ret N
    | _ => error
    end
  | BNZ =>
    match t1 mv with
    | V (P n) => ret N
    | _ => error
    end
  | JAL =>
    match t1 mv with
    | V (P n) => ret N
    | _ => error
    end
  end.

(* There are no (additional) ground rules for this policy *)
