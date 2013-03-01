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

(* Insert load/stores for pseudoregs that got assigned to stack locations. *)

open Misc
open Reg
open Mach

let access_stack r =
  try
    for i = 0 to Array.length r - 1 do
      match r.(i).loc with Stack _ -> raise Exit | _ -> ()
    done;
    false
  with Exit ->
    true

let insert_move src dst next =
  if src.loc = dst.loc
  then next
  else instr_cons (Iop Imove) [|src|] [|dst|] next

let insert_moves src dst next =
  let rec insmoves i =
    if i >= Array.length src
    then next
    else insert_move src.(i) dst.(i) (insmoves (i+1))
  in insmoves 0

class reload_generic = object (self)

val mutable redo_regalloc = false

method makereg r =
  match r.loc with
    Unknown -> fatal_error "Reload.makereg"
  | Reg _ -> r
  | Stack _ ->
      redo_regalloc <- true;
      let newr = Reg.clone r in
      (* Strongly discourage spilling this register *)
      newr.spill_cost <- 100000;
      newr

method private makeregs rv =
  let n = Array.length rv in
  let newv = Array.create n Reg.dummy in
  for i = 0 to n-1 do newv.(i) <- self#makereg rv.(i) done;
  newv

method private makereg1 rv =
  let newv = Array.copy rv in
  newv.(0) <- self#makereg rv.(0);
  newv

method reload_operation op arg res =
  (* By default, assume that arguments and results must reside
     in hardware registers. For moves, allow one arg or one
     res to be stack-allocated, but do something for
     stack-to-stack moves *)
  match op with
    Imove | Ireload | Ispill ->
      begin match arg.(0), res.(0) with
        {loc = Stack s1}, {loc = Stack s2} when s1 <> s2 ->
          ([| self#makereg arg.(0) |], res)
      | _ ->
          (arg, res)
      end
  | _ ->
      (self#makeregs arg, self#makeregs res)

method reload_test tst args =
  self#makeregs args

method private reload i kont =
  match i.desc with
    (* For function calls, returns, etc: the arguments and results are
       already at the correct position (e.g. on stack for some arguments).
       However, something needs to be done for the function pointer in
       indirect calls. *)
    Iend | Ireturn | Iop(Itailcall_imm _) | Iraise -> kont i
  | Iop(Itailcall_ind) ->
      let newarg = self#makereg1 i.arg in
      kont (insert_moves i.arg newarg {i with arg = newarg})
  | Iop(Icall_imm _ | Iextcall _) ->
      self#reload i.next (fun nxt -> kont {i with next = nxt})
  | Iop(Icall_ind) ->
      let newarg = self#makereg1 i.arg in
      self#reload i.next (fun nxt ->
      kont (insert_moves i.arg newarg {i with arg = newarg; next = nxt}))
  | Iop op ->
      let (newarg, newres) = self#reload_operation op i.arg i.res in
      self#reload i.next (fun nxt ->
      kont (insert_moves i.arg newarg
              {i with arg = newarg; res = newres; next =
                  (insert_moves newres i.res nxt)}))
  | Iifthenelse(tst, ifso, ifnot) ->
      let newarg = self#reload_test tst i.arg in
      self#reload ifso (fun nxt_ifso ->
      self#reload ifnot (fun nxt_ifnot ->
      self#reload i.next (fun nxt ->
      kont (insert_moves i.arg newarg
              (instr_cons (Iifthenelse(tst, nxt_ifso, nxt_ifnot))
                 newarg [||] nxt)))))
  | Iswitch(index, cases) ->
      let rec map cases kont = match cases with
        | [] -> kont []
        | case :: rest ->
          self#reload case (fun x ->
          map rest (fun y ->
          kont (x :: y)))
      in
      let newarg = self#makeregs i.arg in
      map (Array.to_list cases) (fun new_cases ->
      self#reload i.next (fun new_nxt ->
      kont (insert_moves i.arg newarg
              (instr_cons (Iswitch(index, Array.of_list new_cases)) newarg [||]
                 new_nxt))))
  | Iloop body ->
      self#reload body (fun new_body ->
      self#reload i.next (fun new_nxt ->
      kont (instr_cons (Iloop(new_body)) [||] [||] new_nxt)))
  | Icatch(nfail, body, handler) ->
      self#reload body (fun new_body ->
      self#reload handler (fun new_handler ->
      self#reload i.next (fun new_nxt ->
      kont (instr_cons(Icatch(nfail,new_body,new_handler)) [||] [||] new_nxt))))
  | Iexit i ->
      kont (instr_cons (Iexit i) [||] [||] dummy_instr)
  | Itrywith(body, handler) ->
      self#reload body (fun new_body ->
      self#reload handler (fun new_handler ->
      self#reload i.next (fun new_nxt ->
      kont (instr_cons (Itrywith(new_body, new_handler)) [||] [||] new_nxt))))

method fundecl f =
  redo_regalloc <- false;
  self#reload f.fun_body (fun new_body ->
  ({fun_name = f.fun_name; fun_args = f.fun_args;
    fun_body = new_body; fun_fast = f.fun_fast;
    fun_dbg  = f.fun_dbg},
   redo_regalloc))

end
