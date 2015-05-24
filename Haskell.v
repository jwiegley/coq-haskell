Require Import Hask.Prelude.
Require Import Hask.Data.IntMap.
Require Import Hask.Data.IntSet.
Require Import Hask.Data.List.
Require Import Hask.Data.NonEmpty.
Require Import Hask.Data.Vector.

Extraction Language Haskell.

Unset Extraction KeepSingleton.
Set Extraction AutoInline.
Set Extraction Optimize.
Set Extraction AccessOpaque.

(* Ssr *)


Extract Inductive unit    => "()" [ "()" ].
Extract Inductive bool    => "Prelude.Bool" ["Prelude.True" "Prelude.False"].
Extract Inductive sumbool => "Prelude.Bool" ["Prelude.True" "Prelude.False"].
Extract Inductive sum     => "Prelude.Either" [ "Prelude.Left" "Prelude.Right" ].
Extract Inductive list    => "[]" ["[]" "(:)"].
Extract Inductive prod    => "(,)" ["(,)"].
Extract Inductive sigT    => "(,)" ["(,)"].
Extract Inductive option  => "Prelude.Maybe" ["Prelude.Just" "Prelude.Nothing"].
Extract Inductive sumor   => "Prelude.Maybe" ["Prelude.Just" "Prelude.Nothing"].

Extract Inductive ordinal => "Prelude.Int" [""].

Extract Inlined Constant addn      => "(Prelude.+)".
Extract Inlined Constant andb      => "(Prelude.&&)".
Extract Inlined Constant app       => "(Prelude.++)".
Extract Inlined Constant cat       => "(Prelude.++)".
Extract Inlined Constant eqb       => "(Prelude.==)".
Extract Inlined Constant eqn       => "(Prelude.==)".
Extract Inlined Constant filter    => "Prelude.filter".
Extract Inlined Constant foldl     => "Data.List.foldl'".
Extract Inlined Constant foldr     => "Prelude.foldr".
Extract Inlined Constant fst       => "Prelude.fst".
Extract Inlined Constant has       => "Data.List.any".
Extract Inlined Constant length    => "Data.List.length".
Extract Inlined Constant leq       => "(Prelude.<=)".
Extract Inlined Constant map       => "Prelude.map".
Extract Inlined Constant maxn      => "Prelude.max".
Extract Inlined Constant minn      => "Prelude.min".
Extract Inlined Constant minus     => "(Prelude.-)".
Extract Inlined Constant mult      => "(Prelude.*)".
Extract Inlined Constant negb      => "Prelude.not".
Extract Inlined Constant orb       => "(Prelude.||)".
Extract Inlined Constant plus      => "(Prelude.+)".
Extract Inlined Constant predn     => "Prelude.pred".
Extract Inlined Constant proj1_sig => "".
Extract Inlined Constant projT1    => "Prelude.fst".
Extract Inlined Constant size      => "Data.List.length".
Extract Inlined Constant snd       => "Prelude.snd".
Extract Inlined Constant subn      => "(Prelude.-)".

Extraction Implicit eq_rect [ x y ].
Extraction Implicit eq_rect_r [ x y ].
Extraction Implicit eq_rec [ x y ].
Extraction Implicit eq_rec_r [ x y ].

Extract Inlined Constant eq_rect => "".
Extract Inlined Constant eq_rect_r => "".
Extract Inlined Constant eq_rec => "".
Extract Inlined Constant eq_rec_r => "".

Extraction Implicit funcomp [ u ].

Extract Inlined Constant funcomp => "(Prelude..)".

Extract Inductive simpl_fun => "(->)" [""].

Extract Inlined Constant fun_of_simpl => "(Prelude.$)".
Extract Inlined Constant SimplRel => "".

Extract Inlined Constant ord_max => "".

Extraction Implicit nat_of_ord [ n ].
Extraction Implicit widen_ord [ n m ].

Extract Inlined Constant nat_of_ord => "".
Extract Inlined Constant widen_ord => "".

Extract Inlined Constant ssr_have => "(Prelude.flip (Prelude.$))".

(* Prelude *)

(** Danger!  Using Int is efficient, but requires we know we won't exceed
    its bounds. *)
Extract Inductive Datatypes.nat => "Prelude.Int" ["0" "(Prelude.succ)"]
  "(\fO fS n -> if n Prelude.<= 0 then fO () else fS (n Prelude.- 1))".

Extract Inductive String.string => "Prelude.String" ["[]" "(:)"].

Extract Inductive comparison =>
  "Prelude.Ordering" ["Prelude.LT" "Prelude.EQ" "Prelude.GT"].

Extract Inlined Constant Arith.Plus.tail_plus => "(Prelude.+)".

Extraction Implicit widen_id [ n ].
Extraction Implicit widen_fst [ n ].

Extract Inlined Constant widen_id           => "".
Extract Inlined Constant widen_fst          => "Prelude.id".

(* Data.IntMap *)

(* Extract Inductive IntMap => "Data.IntMap.IntMap" *)
(*   ["Data.IntMap.fromList"] "(\fS m -> fS m)". *)

Extract Inlined Constant IntMap_mergeWithKey' =>
  "LinearScan.Utils.intMap_mergeWithKey'".

(* Extract Inlined Constant IntMap_lookup       => "Data.IntMap.lookup". *)
(* Extract Inlined Constant IntMap_insert       => "Data.IntMap.insert". *)
(* Extract Inlined Constant IntMap_alter        => "Data.IntMap.alter". *)
(* Extract Inlined Constant IntMap_map          => "Data.IntMap.map". *)
(* Extract Inlined Constant IntMap_foldl        => "Data.IntMap.foldl". *)
(* Extract Inlined Constant IntMap_foldlWithKey => "Data.IntMap.foldlWithKey". *)
(* Extract Inlined Constant IntMap_mergeWithKey => "Data.IntMap.mergeWithKey". *)
(* Extract Inlined Constant IntMap_toList       => "Data.IntMap.toList". *)

(* Data.IntSet *)

(* Extract Inductive IntSet => "Data.IntSet.IntSet" *)
(*   ["Data.IntSet.fromList"] "(\fS m -> fS m)". *)

(* Extract Inlined Constant IntSet_member     => "Data.IntSet.member". *)
(* Extract Inlined Constant IntSet_insert     => "Data.IntSet.insert". *)
(* Extract Inlined Constant IntSet_delete     => "Data.IntSet.delete". *)
(* Extract Inlined Constant IntSet_union      => "Data.IntSet.union". *)
(* Extract Inlined Constant IntSet_difference => "Data.IntSet.difference". *)
(* Extract Inlined Constant IntSet_foldl      => "Data.IntSet.foldl'". *)

(* Data.List *)

Extract Inlined Constant safe_hd => "Prelude.head".
Extract Inlined Constant sumlist => "Data.List.sum".
(* Extract Inlined Constant lebf    => "Data.Ord.comparing". *)
(* Extract Inlined Constant insert  => "Data.List.insertBy". *)

Extract Inlined Constant List.destruct_list => "LinearScan.Utils.uncons".
Extract Inlined Constant list_membership    => "Prelude.const".

(* Data.NonEmpty *)

Extract Inductive NonEmpty => "[]" ["(:[])" "(:)"]
  "(\ns nc l -> case l of [x] -> ns x; (x:xs) -> nc x xs)".

Extract Inlined Constant NE_length  => "Prelude.length".
Extract Inlined Constant NE_to_list => "".
Extract Inlined Constant NE_head    => "Prelude.head".
Extract Inlined Constant NE_last    => "Prelude.last".
Extract Inlined Constant NE_map     => "Prelude.map".
Extract Inlined Constant NE_foldl   => "Data.List.foldl'".

(* Data.Vector *)

Extract Constant Vec "a" => "[]".
Extraction Inline Vec.

Extract Inlined Constant vnil     => "[]".
Extract Inlined Constant vsing    => "[]".
Extract Inlined Constant vcons    => "(:)".
Extract Inlined Constant vshiftin => "LinearScan.Utils.snoc".
Extract Inlined Constant vreplace => "LinearScan.Utils.set_nth".
Extract Inlined Constant vec_rect => "LinearScan.Utils.list_rect".
Extract Inlined Constant vconst   => "Data.List.replicate".
Extract Inlined Constant vfoldl   => "LinearScan.Utils.vfoldl'".
Extract Inlined Constant vapp     => "Prelude.(++)".
Extract Inlined Constant vmap     => "LinearScan.Utils.vmap".
Extract Inlined Constant vnth     => "LinearScan.Utils.nth".

Extract Inlined Constant vfoldl_with_index
  => "(LinearScan.Utils.vfoldl'_with_index)".

Extraction Blacklist String List Vector NonEmpty.
