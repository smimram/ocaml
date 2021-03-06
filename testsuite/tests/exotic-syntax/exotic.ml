(* Exotic OCaml syntax constructs found in the manual that are not *)
(* used in the source of the OCaml distribution (even in the tests). *)

(* Spaces between the parts of the ?label: token in a typexpr. *)
type t = ? label : int -> int -> int;;

(* Lazy in a pattern. *)
let f x =
  match x with lazy y -> y
;;

(* Spaces between the parts of the ?label: token in a class-type. *)
class c1 =
  (fun ?label:x y -> object end : ? label : int -> int -> object end)
;;

(* type-class annotation in class-expr *)
class c2 = (object end : object end);;

(* virtual object field *)
class virtual c3 = object val virtual x : int end;;
class virtual c4 = object val mutable virtual x : int end;;

(* abstract module type in a signature *)
module type T = sig
  module type U
end;;

(* associativity rules for patterns *)
match Some (Some 1) with Some Some x -> x;;
match Some (`Tag 1) with Some `Tag x -> x;;
match `Tag (Some 1) with `Tag Some x -> x;;
match `Tag (`Tag 1) with `Tag `Tag x -> x;;


(* Even more exotic: not even found in the manual, but used in some *)
(* programs in testsuite/external/. *)

(* local functor *)
let module M (M1 : sig end) (M2 : sig end) = struct end in ();;

(* let-binding with a type coercion *)
let f x :> int = x + 1;;
let f x : int :> int = x + 1;;

(* "begin end" as an alias for "()" *)
let x = begin end;;
