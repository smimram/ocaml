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

(* Liveness analysis.
   Annotate mach code with the set of regs live at each point. *)

open Mach

let live_at_exit = ref []
let find_live_at_exit k =
  try
    List.assoc k !live_at_exit
  with
  | Not_found -> Misc.fatal_error "Spill.find_live_at_exit"

let live_at_break = ref Reg.Set.empty
let live_at_raise = ref Reg.Set.empty

let rec live i finally kont =
  (* finally is the set of registers live after execution of the
     instruction sequence.
     The result of the function is the set of registers live just
     before the instruction sequence.
     The instruction i is annotated by the set of registers live across
     the instruction. *)
  match i.desc with
    Iend ->
      i.live <- finally;
      kont finally
  | Ireturn | Iop(Itailcall_ind) | Iop(Itailcall_imm _) ->
      (* i.live remains empty since no regs are live across *)
      kont (Reg.set_of_array i.arg)
  | Iifthenelse(test, ifso, ifnot) ->
      live i.next finally (fun at_join ->
      live ifso at_join (fun s1 ->
      live ifnot at_join (fun s2 ->
      let at_fork = Reg.Set.union s1 s2 in
      i.live <- at_fork;
      kont (Reg.add_set_array at_fork i.arg))))
  | Iswitch(index, cases) ->
      live i.next finally (fun at_join ->
      let case_nb = Array.length cases in
      let rec fold i acc kont =
        if i = case_nb then kont acc else
          live cases.(i) at_join (fun case_set ->
          fold (i + 1) (Reg.Set.union acc case_set) kont)
      in
      fold 0 Reg.Set.empty (fun at_fork ->
      i.live <- at_fork;
      kont (Reg.add_set_array at_fork i.arg)))
  | Iloop(body) ->
      (* Yes, there are better algorithms, but we'll just iterate till
         reaching a fixpoint. *)
      let rec fixpoint at_top kont =
        live body at_top (fun set ->
        let new_at_top = Reg.Set.union at_top set in
        if Reg.Set.equal at_top new_at_top then kont at_top
        else fixpoint new_at_top kont)
      in
      fixpoint Reg.Set.empty (fun at_top -> i.live <- at_top; kont at_top)
  | Icatch(nfail, body, handler) ->
      live i.next finally (fun at_join ->
      live handler at_join (fun before_handler ->
      live_at_exit := (nfail,before_handler) :: !live_at_exit;
      live body at_join (fun before_body ->
      live_at_exit := List.tl !live_at_exit;
      i.live <- before_body;
      kont before_body)))
  | Iexit nfail ->
      let this_live = find_live_at_exit nfail in
      i.live <- this_live ;
      kont this_live
  | Itrywith(body, handler) ->
      live i.next finally (fun at_join ->
      live handler at_join (fun before_handler ->
      let saved_live_at_raise = !live_at_raise in
      live_at_raise := Reg.Set.remove Proc.loc_exn_bucket before_handler;
      live body at_join (fun before_body ->
      live_at_raise := saved_live_at_raise;
      i.live <- before_body;
      kont before_body)))
  | Iraise ->
      (* i.live remains empty since no regs are live across *)
      kont (Reg.add_set_array !live_at_raise i.arg)
  | _ ->
      live i.next finally (fun set ->
      let across_after = Reg.diff_set_array set i.res in
      let across =
        match i.desc with
            Iop Icall_ind | Iop(Icall_imm _) | Iop(Iextcall _)
          | Iop(Iintop Icheckbound) | Iop(Iintop_imm(Icheckbound, _)) ->
                (* The function call may raise an exception, branching to the
                   nearest enclosing try ... with. Similarly for bounds checks.
                   Hence, everything that must be live at the beginning of
                   the exception handler must also be live across this instr. *)
            Reg.Set.union across_after !live_at_raise
          | _ ->
            across_after
      in
      i.live <- across;
      kont (Reg.add_set_array across i.arg))

let fundecl ppf f =
  live f.fun_body Reg.Set.empty (fun initially_live ->
  (* Sanity check: only function parameters can be live at entrypoint *)
  let wrong_live =
    Reg.Set.diff initially_live (Reg.set_of_array f.fun_args)
  in
  if not (Reg.Set.is_empty wrong_live) then begin
    Format.fprintf ppf "%a@." Printmach.regset wrong_live;
    Misc.fatal_error "Liveness.fundecl"
  end)
