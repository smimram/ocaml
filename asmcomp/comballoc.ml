(***********************************************************************)
(*                                                                     *)
(*                                OCaml                                *)
(*                                                                     *)
(*            Xavier Leroy, projet Cristal, INRIA Rocquencourt         *)
(*                                                                     *)
(*  Copyright 1999 Institut National de Recherche en Informatique et   *)
(*  en Automatique.  All rights reserved.  This file is distributed    *)
(*  under the terms of the Q Public License version 1.0.               *)
(*                                                                     *)
(***********************************************************************)

(* Combine heap allocations occurring in the same basic block *)

open Mach

type allocation_state =
    No_alloc                            (* no allocation is pending *)
  | Pending_alloc of Reg.t * int        (* an allocation is pending *)
(* The arguments of Pending_alloc(reg, ofs) are:
     reg  the register holding the result of the last allocation
     ofs  the alloc position in the allocated block *)

let allocated_size = function
    No_alloc -> 0
  | Pending_alloc(reg, ofs) -> ofs

let rec combine i allocstate kont =
  match i.desc with
    Iend | Ireturn | Iexit _ | Iraise ->
      kont (i, allocated_size allocstate)
  | Iop(Ialloc sz) ->
      begin match allocstate with
        No_alloc ->
          combine i.next (Pending_alloc(i.res.(0), sz)) (fun (newnext, newsz) ->
          kont (instr_cons (Iop(Ialloc newsz)) i.arg i.res newnext, 0))
      | Pending_alloc(reg, ofs) ->
          if ofs + sz < Config.max_young_wosize * Arch.size_addr then begin
            combine i.next (Pending_alloc(reg, ofs + sz))
              (fun (newnext, newsz) ->
                kont (instr_cons (Iop(Iintop_imm(Iadd, ofs))) [| reg |]
                        i.res newnext, newsz))
          end else begin
            combine i.next (Pending_alloc(i.res.(0), sz))
              (fun (newnext, newsz) ->
                kont (instr_cons (Iop(Ialloc newsz)) i.arg i.res newnext, ofs))
          end
      end
  | Iop(Icall_ind | Icall_imm _ | Iextcall _ |
        Itailcall_ind | Itailcall_imm _) ->
      combine_restart i.next (fun newnext ->
      kont (instr_cons_debug i.desc i.arg i.res i.dbg newnext,
            allocated_size allocstate))
  | Iop op ->
      combine i.next allocstate (fun (newnext, sz) ->
      kont (instr_cons_debug i.desc i.arg i.res i.dbg newnext, sz))
  | Iifthenelse(test, ifso, ifnot) ->
      combine_restart ifso (fun newifso ->
      combine_restart ifnot (fun newifnot ->
      combine_restart i.next (fun newnext ->
      kont (instr_cons (Iifthenelse(test, newifso, newifnot))
              i.arg i.res newnext, allocated_size allocstate))))
  | Iswitch(table, cases) ->
    let rec map l kont = match l with
      | [] -> kont []
      | hd :: tl ->
        combine_restart hd (fun x ->
        map tl (fun y ->
        kont (x :: y)))
    in
    map (Array.to_list cases) (fun newcases ->
    combine_restart i.next (fun newnext ->
    kont (instr_cons (Iswitch(table, Array.of_list newcases))
            i.arg i.res newnext, allocated_size allocstate)))
  | Iloop(body) ->
      combine_restart body (fun newbody ->
      kont (instr_cons (Iloop(newbody)) i.arg i.res i.next,
            allocated_size allocstate))
  | Icatch(io, body, handler) ->
      combine body allocstate (fun (newbody, sz) ->
      combine_restart handler (fun newhandler ->
      combine_restart i.next (fun newnext ->
      kont (instr_cons (Icatch(io, newbody, newhandler))
              i.arg i.res newnext, sz))))
  | Itrywith(body, handler) ->
      combine body allocstate (fun (newbody, sz) ->
      combine_restart handler (fun newhandler ->
      combine_restart i.next (fun newnext ->
      kont (instr_cons (Itrywith(newbody, newhandler))
              i.arg i.res newnext, sz))))

and combine_restart i kont =
  combine i No_alloc (fun (newi, _) -> kont newi)

let fundecl f =
  combine_restart f.fun_body (fun r -> {f with fun_body = r})
