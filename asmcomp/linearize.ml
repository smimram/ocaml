(***********************************************************************)
(*                                                                     *)
(*                                OCaml                                *)
(*                                                                     *)
(*            Xavier Leroy, projet Cristal, INRIA Rocquencourt         *)
(*                                                                     *)
(*  Copyright 1996 Institut National de Recherche en Informatique et   *)
(*  en Automatique.  All rights reserved.  This file is distributed    *)
(*  under the terms of the Q Public License version 1.0.               *)
(*                                                                     *)
(***********************************************************************)

(* Transformation of Mach code into a list of pseudo-instructions. *)

open Reg
open Mach

type label = int

let label_counter = ref 99

let new_label() = incr label_counter; !label_counter

type instruction =
  { mutable desc: instruction_desc;
    mutable next: instruction;
    arg: Reg.t array;
    res: Reg.t array;
    dbg: Debuginfo.t;
    live: Reg.Set.t }

and instruction_desc =
    Lend
  | Lop of operation
  | Lreloadretaddr
  | Lreturn
  | Llabel of label
  | Lbranch of label
  | Lcondbranch of test * label
  | Lcondbranch3 of label option * label option * label option
  | Lswitch of label array
  | Lsetuptrap of label
  | Lpushtrap
  | Lpoptrap
  | Lraise

let has_fallthrough = function
  | Lreturn | Lbranch _ | Lswitch _ | Lraise
  | Lop Itailcall_ind | Lop (Itailcall_imm _) -> false
  | _ -> true

type fundecl =
  { fun_name: string;
    fun_body: instruction;
    fun_fast: bool;
    fun_dbg : Debuginfo.t }

(* Invert a test *)

let invert_integer_test = function
    Isigned cmp -> Isigned(Cmm.negate_comparison cmp)
  | Iunsigned cmp -> Iunsigned(Cmm.negate_comparison cmp)

let invert_test = function
    Itruetest -> Ifalsetest
  | Ifalsetest -> Itruetest
  | Iinttest(cmp) -> Iinttest(invert_integer_test cmp)
  | Iinttest_imm(cmp, n) -> Iinttest_imm(invert_integer_test cmp, n)
  | Ifloattest(cmp, neg) -> Ifloattest(cmp, not neg)
  | Ieventest -> Ioddtest
  | Ioddtest -> Ieventest

(* The "end" instruction *)

let rec end_instr =
  { desc = Lend;
    next = end_instr;
    arg = [||];
    res = [||];
    dbg = Debuginfo.none;
    live = Reg.Set.empty }

(* Cons an instruction (live, debug empty) *)

let instr_cons d a r n =
  { desc = d; next = n; arg = a; res = r;
    dbg = Debuginfo.none; live = Reg.Set.empty }

(* Cons a simple instruction (arg, res, live empty) *)

let cons_instr d n =
  { desc = d; next = n; arg = [||]; res = [||];
    dbg = Debuginfo.none; live = Reg.Set.empty }

(* Build an instruction with arg, res, dbg, live taken from
   the given Mach.instruction *)

let copy_instr d i n =
  { desc = d; next = n;
    arg = i.Mach.arg; res = i.Mach.res;
    dbg = i.Mach.dbg; live = i.Mach.live }

(*
   Label the beginning of the given instruction sequence.
   - If the sequence starts with a branch, jump over it.
   - If the sequence is the end, (tail call position), just do nothing
*)

let get_label n = match n.desc with
    Lbranch lbl -> (lbl, n)
  | Llabel lbl -> (lbl, n)
  | Lend -> (-1, n)
  | _ -> let lbl = new_label() in (lbl, cons_instr (Llabel lbl) n)

(* Check the fallthrough label *)
let check_label n = match n.desc with
  | Lbranch lbl -> lbl
  | Llabel lbl -> lbl
  | _ -> -1

(* Discard all instructions up to the next label.
   This function is to be called before adding a non-terminating
   instruction. *)

let rec discard_dead_code n =
  match n.desc with
    Lend -> n
  | Llabel _ -> n
(* Do not discard Lpoptrap or Istackoffset instructions,
   as this may cause a stack imbalance later during assembler generation. *)
  | Lpoptrap -> n
  | Lop(Istackoffset _) -> n
  | _ -> discard_dead_code n.next

(*
   Add a branch in front of a continuation.
   Discard dead code in the continuation.
   Does not insert anything if we're just falling through
   or if we jump to dead code after the end of function (lbl=-1)
*)

let add_branch lbl n =
  if lbl >= 0 then
    let n1 = discard_dead_code n in
    match n1.desc with
    | Llabel lbl1 when lbl1 = lbl -> n1
    | _ -> cons_instr (Lbranch lbl) n1
  else
    discard_dead_code n

(* Current labels for exit handler *)

let exit_label = ref []

let find_exit_label k =
  try
    List.assoc k !exit_label
  with
  | Not_found -> Misc.fatal_error "Linearize.find_exit_label"

let is_next_catch n = match !exit_label with
| (n0,_)::_  when n0=n -> true
| _ -> false

(* Linearize an instruction [i]: add it in front of the continuation [n] *)

let rec linear i n kont =
  match i.Mach.desc with
    Iend -> kont n
  | Iop(Itailcall_ind | Itailcall_imm _ as op) ->
      kont (copy_instr (Lop op) i (discard_dead_code n))
  | Iop(Imove | Ireload | Ispill)
    when i.Mach.arg.(0).loc = i.Mach.res.(0).loc ->
      linear i.Mach.next n kont
  | Iop op ->
      linear i.Mach.next n (fun new_n -> kont (copy_instr (Lop op) i new_n))
  | Ireturn ->
      let n1 = copy_instr Lreturn i (discard_dead_code n) in
      if !Proc.contains_calls
      then kont (cons_instr Lreloadretaddr n1)
      else kont n1
  | Iifthenelse(test, ifso, ifnot) ->
      linear i.Mach.next n (fun n1 ->
      begin match (ifso.Mach.desc, ifnot.Mach.desc, n1.desc) with
        Iend, _, Lbranch lbl ->
          linear ifnot n1 (fun x ->
          kont (copy_instr (Lcondbranch(test, lbl)) i x))
      | _, Iend, Lbranch lbl ->
          linear ifso n1 (fun x ->
          kont (copy_instr (Lcondbranch(invert_test test, lbl)) i x))
      | Iexit nfail1, Iexit nfail2, _
            when is_next_catch nfail1 ->
          let lbl2 = find_exit_label nfail2 in
          linear ifso n1 (fun x ->
          kont (copy_instr (Lcondbranch (invert_test test, lbl2)) i x))
      | Iexit nfail, _, _ ->
          linear ifnot n1 (fun n2 ->
          let lbl = find_exit_label nfail in
          kont (copy_instr (Lcondbranch(test, lbl)) i n2))
      | _,  Iexit nfail, _ ->
          linear ifso n1 (fun n2 ->
          let lbl = find_exit_label nfail in
          kont (copy_instr (Lcondbranch(invert_test test, lbl)) i n2))
      | Iend, _, _ ->
          let (lbl_end, n2) = get_label n1 in
          linear ifnot n2 (fun x ->
          kont (copy_instr (Lcondbranch(test, lbl_end)) i x))
      | _,  Iend, _ ->
          let (lbl_end, n2) = get_label n1 in
          linear ifso n2 (fun x ->
          kont (copy_instr (Lcondbranch(invert_test test, lbl_end)) i x))
      | _, _, _ ->
        (* Should attempt branch prediction here *)
          let (lbl_end, n2) = get_label n1 in
          linear ifnot n2 (fun x ->
          let (lbl_else, nelse) = get_label x in
          linear ifso (add_branch lbl_end nelse) (fun y ->
          kont (copy_instr (Lcondbranch(invert_test test, lbl_else)) i y)))
      end)
  | Iswitch(index, cases) ->
      let lbl_cases = Array.create (Array.length cases) 0 in
      linear i.Mach.next n (fun x ->
      let (lbl_end, n1) = get_label x in
      let n2 = ref (discard_dead_code n1) in
      let rec rev_iter i kont =
        if i >= 0 then (
          linear cases.(i) (add_branch lbl_end !n2) (fun y ->
          let (lbl_case, ncase) = get_label y in
          lbl_cases.(i) <- lbl_case;
          n2 := discard_dead_code ncase;
          rev_iter (i - 1) kont)
        ) else kont ()
      in
      rev_iter (Array.length cases - 1) (fun () ->
      (* Switches with 1 and 2 branches have been eliminated earlier.
         Here, we do something for switches with 3 branches. *)
      if Array.length index = 3 then begin
        let fallthrough_lbl = check_label !n2 in
        let find_label n =
          let lbl = lbl_cases.(index.(n)) in
          if lbl = fallthrough_lbl then None else Some lbl in
        kont (copy_instr (Lcondbranch3(find_label 0, find_label 1,
                                       find_label 2)) i !n2)
      end else
        kont (copy_instr (Lswitch(Array.map (fun n -> lbl_cases.(n)) index))
                i !n2)))
  | Iloop body ->
      let lbl_head = new_label() in
      linear i.Mach.next n (fun n1 ->
      linear body (cons_instr (Lbranch lbl_head) n1) (fun n2 ->
      kont (cons_instr (Llabel lbl_head) n2)))
  | Icatch(io, body, handler) ->
      linear i.Mach.next n (fun x ->
      let (lbl_end, n1) = get_label x in
      linear handler n1 (fun y ->
      let (lbl_handler, n2) = get_label y in
      exit_label := (io, lbl_handler) :: !exit_label ;
      linear body (add_branch lbl_end n2) (fun n3 ->
      exit_label := List.tl !exit_label;
      kont n3)))
  | Iexit nfail ->
      linear i.Mach.next n (fun n1 ->
      let lbl = find_exit_label nfail in
      kont (add_branch lbl n1))
  | Itrywith(body, handler) ->
      linear i.Mach.next n (fun x ->
      let (lbl_join, n1) = get_label x in
      linear body (cons_instr Lpoptrap n1) (fun y ->
      let (lbl_body, n2) = get_label (cons_instr Lpushtrap y) in
      linear handler (add_branch lbl_join n2) (fun z ->
      kont (cons_instr (Lsetuptrap lbl_body) z))))
  | Iraise ->
      kont (copy_instr Lraise i (discard_dead_code n))

let fundecl f =
  linear f.Mach.fun_body end_instr (fun body ->
  { fun_name = f.Mach.fun_name;
    fun_body = body;
    fun_fast = f.Mach.fun_fast;
    fun_dbg  = f.Mach.fun_dbg })
