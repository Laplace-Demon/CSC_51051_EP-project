open Format
let () = Printexc.record_backtrace true

(** Type variables. *)
type tvar = string

(** Term variables. *)
type var = string

(** Types. *)
type ty =
  | TVar of tvar
  | Impl of ty * ty

type tm =
  | Var of var
  | App of tm * tm
  | Abs of var * ty * tm

let rec string_of_ty : ty -> string = function
  | TVar tvar ->
    sprintf "%s" tvar
  | Impl (ty1, ty2) ->
    sprintf "(%s => %s)" (string_of_ty ty1) (string_of_ty ty2)

let rec string_of_tm : tm -> string = function
  | Var var ->
    sprintf "%s" var
  | App (tm1, tm2) ->
    sprintf "(%s %s)" (string_of_tm tm1) (string_of_tm tm2)
  | Abs (var, ty, tm) ->
    sprintf "(fun (%s : %s) -> %s)" var (string_of_ty ty) (string_of_tm tm)

(** Typing contexts. *)
type context = (var * ty) list

let empty_context : context = []

exception Type_error

(** Typing rules.
    
    -------------------(ax)
        Γ ⊢ t : Γ(t)

      Γ ⊢ t1 : A -> B   Γ ⊢ t2 : A
    --------------------------------(app)
      Γ ⊢ App (t1, t2) : B

Γ, v : ty ⊢ t : A
------------------(abs)
Γ ⊢ Abs (v, ty, t) : ty -> A

*)

(** Type inference. *)
let rec infer_type : context -> tm -> ty = fun cont -> function
  | Var var ->
    begin try List.assoc var cont with
    | Not_found ->
      raise Type_error
    end
  | App (tm1, tm2) ->
    begin match infer_type cont tm1, infer_type cont tm2 with
    | Impl (a1, b), a2 when a1 = a2 ->
      b
    | _, _ ->
      raise Type_error
    end
  | Abs (var, ty, tm) ->
    let res_ty = infer_type ((var, ty) :: cont) tm in
    Impl (ty, res_ty)

let () =
  let tm = Abs ("f", Impl (TVar "A", TVar "B"), Abs ("g", Impl (TVar "B", TVar "C") , Abs ("x", TVar "A", App (Var "g", App (Var "f", Var "x"))))) in
  let ty = Impl (Impl (TVar "A", TVar "B"), Impl (Impl (TVar "B", TVar "C"), Impl (TVar "A", TVar "C"))) in
  assert (infer_type empty_context tm = ty)

let () =
  let tm = Abs ("f", TVar "A", Var "x") in
  try
    let _ = infer_type empty_context tm in
    assert false
  with
  | Type_error -> ()

let () =
  let tm = Abs ("f", TVar "A", Abs ("x", TVar "B", App (Var "f", Var "x"))) in
  try
    let _ = infer_type empty_context tm in
    assert false
  with
  | Type_error -> ()

let () =
  let tm = Abs ("f", Impl (TVar "A", TVar "B"), Abs ("x", TVar "B", App (Var "f", Var "x"))) in
  try
    let _ = infer_type empty_context tm in
    assert false
  with
  | Type_error -> ()

(** Type checking. *)
let check_type : context -> tm -> ty -> unit = fun cont tm ty ->
  try
    if infer_type cont tm = ty
    then ()
    else raise Type_error
  with
  | Type_error -> raise Type_error

let () =
  let tm = Abs ("x", TVar "A", Var "x") in
  let ty = Impl (TVar "A", TVar "A") in
  check_type empty_context tm ty

let () =
  let tm = Abs ("x", TVar "A", Var "x") in
  let ty = Impl (TVar "B", TVar "B") in
  try
    check_type empty_context tm ty;
    assert false
  with
  | Type_error -> ()

let () =
  let tm = Var "x" in
  let ty = TVar "A" in
  try
    check_type empty_context tm ty;
    assert false
  with
  | Type_error -> ()
