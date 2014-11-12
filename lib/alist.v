Require Import ssreflect ssrbool ssrfun eqtype seq.
Require Import partial_maps.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Module AList.

Section Basic.

Variable T : eqType.

Section FixS.

Variable S : Type.

Record alist := AList {
  get_alist : seq (T * S)
}.

Fixpoint get_int (s : seq (T * S)) (k : T) : option S :=
  match s with
  | [::] => None
  | (k', v) :: s => if k' == k then Some v else get_int s k
  end.

Definition get (al : alist) (k : T) : option S :=
  get_int (get_alist al) k.

Definition set (al : alist) k v : alist :=
  AList ((k, v) :: get_alist al).

Definition remove (s : alist) (k : T) : alist :=
  AList [seq x | x <- get_alist s & x.1 != k].

Definition empty : alist := AList [::].

Definition is_empty (al : alist) : bool :=
  nilp (get_alist al).

End FixS.

Fixpoint map_filter_int S1 S2 (f : S1 -> option S2) (s : seq (T * S1)) : seq (T * S2) :=
  match s with
  | [::] => [::]
  | (k, v) :: s =>
    match f v with
    | Some v' => (k, v') :: map_filter_int f s
    | None => [seq x | x <- map_filter_int f s & x.1 != k]
    end
  end.

Definition map_filter S1 S2 (f : S1 -> option S2) (al : alist S1) : alist S2 :=
  AList (map_filter_int f (get_alist al)).

Fixpoint get_and_remove S (s : seq (T * S)) k : option S * seq (T * S) :=
  match s with
  | [::] => (None, s)
  | (k', v) :: s => if k' == k then (Some v, [seq x | x <- s & x.1 != k])
                    else let res := get_and_remove s k in
                         (res.1, (k', v) :: res.2)
  end.

Fixpoint combine_int S1 S2 S3 (f : option S1 -> option S2 -> option S3)
                              (s1 : seq (T * S1)) (s2 : seq (T * S2)) : seq (T * S3) :=
  match s1 with
  | [::] => pmap (fun x => omap (pair x.1) (f None (Some x.2))) s2
  | (k, v) :: s1 => let res := get_and_remove s2 k in
                    let rec := combine_int f s1 res.2 in
                    match f (Some v) res.1 with
                    | Some v' => (k, v') :: rec
                    | None => combine_int f s1 res.2
                    end
  end.

Definition combine S1 S2 S3 (f : option S1 -> option S2 -> option S3) al1 al2 :=
  AList (combine_int f (get_alist al1) (get_alist al2)).

End Basic.

End AList.

Global Instance alist_partial_map T : PartMaps.partial_map (AList.alist T) T := {
  get := @AList.get T;
  set := @AList.set T;
  map_filter := @AList.map_filter T;
  remove := @AList.remove T;
  combine := @AList.combine T;
  empty := @AList.empty T;
  is_empty := @AList.is_empty T
}.
