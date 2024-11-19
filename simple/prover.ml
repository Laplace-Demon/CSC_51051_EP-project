open Format
open Expr

let () = Printexc.record_backtrace true

let ty_of_string s = Parser.ty Lexer.token (Lexing.from_string s)

let tm_of_string s = Parser.tm Lexer.token (Lexing.from_string s)

let rec string_of_ty : ty -> string = function
  | TVar tvar ->
    sprintf "%s" tvar
  | Impl (ty1, ty2) ->
    sprintf "(%s ⇒ %s)" (string_of_ty ty1) (string_of_ty ty2)
  | Conj (ty1, ty2) ->
    sprintf "(%s ∧ %s)" (string_of_ty ty1) (string_of_ty ty2)
  | Disj (ty1, ty2) ->
    sprintf "(%s ∨ %s)" (string_of_ty ty1) (string_of_ty ty2)
  | True ->
    sprintf "⊤"
  | False ->
    sprintf "⊥"
  | Nat ->
    sprintf "Nat"

let () =
  let ty = Impl (Impl (TVar "A", TVar "B"), Impl (TVar "A", TVar "C")) in
  printf "%s\n" (string_of_ty ty)

let rec string_of_tm : tm -> string = function
  | Var var ->
    sprintf "%s" var
  | App (tm1, tm2) ->
    sprintf "(%s %s)" (string_of_tm tm1) (string_of_tm tm2)
  | Abs (var, ty, tm) ->
    sprintf "(λ (%s : %s) → %s)" var (string_of_ty ty) (string_of_tm tm)
  | Pair (tm1, tm2) ->
    sprintf "(%s, %s)" (string_of_tm tm1) (string_of_tm tm2)
  | Fst tm ->
    sprintf "fst(%s)" (string_of_tm tm)
  | Snd tm ->
    sprintf "snd(%s)" (string_of_tm tm)
  | Left (tm, ty) ->
    sprintf "left(%s, %s)" (string_of_tm tm) (string_of_ty ty)
  | Right (ty, tm) ->
    sprintf "right(%s, %s)" (string_of_ty ty) (string_of_tm tm)
  | Case (tm, lv, lb, rv, rb) ->
    sprintf "case %s of %s -> %s | %s -> %s)" (string_of_tm tm) lv (string_of_tm lb) rv (string_of_tm rb)
  | Unit ->
    sprintf "()"
  | Absurd (tm, ty) ->
    sprintf "absurd(%s, %s)" (string_of_tm tm) (string_of_ty ty)
  | Zero ->
    sprintf "zero"
  | Suc tm ->
    sprintf "suc(%s)" (string_of_tm tm)
  | Rec (tm, base, nv, rv, recr) ->
    sprintf "rec(%s, %s, %s %s -> %s)" (string_of_tm tm) (string_of_tm base) nv rv (string_of_tm recr)

let () =
  let tm = Abs ("f", Impl (TVar "A", TVar "B"), Abs ("x", TVar "A", App (Var "f", Var "x"))) in
  printf "%s\n" (string_of_tm tm)

(** Typing contexts. *)
type context = (var * ty) list

let empty_env : context = []

exception Type_error

(** Typing rules.

         -------------------(ax)
              Γ ⊢ t : Γ(t)

      Γ ⊢ t : A -> B   Γ ⊢ u : A
    --------------------------------(app)
          Γ ⊢ App (t, u) : B

            Γ, v : A ⊢ t : B
      ------------------------------(abs)
        Γ ⊢ Abs (v, A, t) : A -> B

          Γ ⊢ t : A   Γ ⊢ u : B
      ----------------------------(pair)
         Γ ⊢ Pair (t, u) : A /\ B

              Γ ⊢ t : A /\ B
          --------------------(fst)
              Γ ⊢ Fst t : A

              Γ ⊢ t : A /\ B
          --------------------(snd)
              Γ ⊢ Snd t : B

                Γ ⊢ t : A
        --------------------------(left)
          Γ ⊢ Left (t, B) : A \/ B

                Γ ⊢ t : B
        ----------------------------(right)
          Γ ⊢ Right (A, t) : A \/ B

    Γ ⊢ t : A \/ B   Γ, x : A ⊢ u : C   Γ, y : B ⊢ v : C
----------------------------------------------------------(case)
          Γ ⊢ Case (t, x, u, y, v) : C

            ---------------(unit)
              Γ ⊢ Unit : ⊤

                Γ ⊢ t : ⊥
      --------------------------(absurd)
          Γ ⊢ Absurd (t, A) : A

          ------------------(zero)
            Γ ⊢ Zero : Nat

              Γ ⊢ t : Nat
         -------------------(suc)
            Γ ⊢ Suc t : Nat

 Γ ⊢ t : Nat   Γ ⊢ u : A   Γ, x : Nat, y : A ⊢ v : A
-----------------------------------------------------(rec)
        Γ ⊢ Rec (t, u, x, y, v) : A
*)

(** Type inference. *)
let rec infer_type : context -> tm -> ty = fun env -> function
  | Var var ->
    begin try List.assoc var env with
    | Not_found ->
      raise Type_error
    end
  | App (tm1, tm2) ->
    begin match infer_type env tm1 with
    | Impl (a, b) ->
      check_type env tm2 a;
      b
    | _ ->
      raise Type_error
    end
  | Abs (var, ty, tm) ->
    let res_ty = infer_type ((var, ty) :: env) tm in
    Impl (ty, res_ty)
  | Pair (tm1, tm2) ->
    Conj (infer_type env tm1, infer_type env tm2)
  | Fst tm ->
    begin match infer_type env tm with
    | Conj (a, _) ->
      a
    | _ ->
      raise Type_error
    end
  | Snd tm ->
    begin match infer_type env tm with
    | Conj (_, b) ->
      b
    | _ ->
      raise Type_error
    end
  | Left (tm, ty) ->
    Disj (infer_type env tm, ty)
  | Right (ty, tm) ->
    Disj (ty, infer_type env tm)
  | Case (tm, lv, lb, rv, rb) ->
    begin match infer_type env tm with
    | Disj (a, b) ->
      begin match infer_type ((lv, a) :: env) lb, infer_type ((rv, b) :: env) rb with
      | c1, c2 when c1 = c2 ->
        c1
      | _, _ ->
        raise Type_error
      end
    | _ ->
      raise Type_error
    end
  | Unit ->
    True
  | Absurd (tm, ty) ->
    check_type env tm False;
    ty
  | Zero ->
    Nat
  | Suc tm ->
    check_type env tm Nat;
    Nat
  | Rec (tm, base, vn, vr, recr) ->
    check_type env tm Nat;
    let ty = infer_type env base in
    check_type ((vn, Nat) :: (vr, ty) :: env) recr ty;
    ty

(** Type checking. *)
and check_type : context -> tm -> ty -> unit = fun env tm ty ->
  if infer_type env tm = ty
  then ()
  else raise Type_error

let () =
  let tm = Abs ("f", Impl (TVar "A", TVar "B"), Abs ("g", Impl (TVar "B", TVar "C") , Abs ("x", TVar "A", App (Var "g", App (Var "f", Var "x"))))) in
  let ty = Impl (Impl (TVar "A", TVar "B"), Impl (Impl (TVar "B", TVar "C"), Impl (TVar "A", TVar "C"))) in
  assert (infer_type empty_env tm = ty)

let () =
  let tm = Abs ("f", TVar "A", Var "x") in
  try
    let _ = infer_type empty_env tm in
    assert false
  with
  | Type_error -> ()

let () =
  let tm = Abs ("f", TVar "A", Abs ("x", TVar "B", App (Var "f", Var "x"))) in
  try
    let _ = infer_type empty_env tm in
    assert false
  with
  | Type_error -> ()

let () =
  let tm = Abs ("f", Impl (TVar "A", TVar "B"), Abs ("x", TVar "B", App (Var "f", Var "x"))) in
  try
    let _ = infer_type empty_env tm in
    assert false
  with
  | Type_error -> ()

let () =
  let tm = Abs ("x", TVar "A", Var "x") in
  let ty = Impl (TVar "A", TVar "A") in
  check_type empty_env tm ty

let () =
  let tm = Abs ("x", TVar "A", Var "x") in
  let ty = Impl (TVar "B", TVar "B") in
  try
    check_type empty_env tm ty;
    assert false
  with
  | Type_error -> ()

let () =
  let tm = Var "x" in
  let ty = TVar "A" in
  try
    check_type empty_env tm ty;
    assert false
  with
  | Type_error -> ()

let and_comm : tm =
  Abs ("p",  Conj (TVar "A", TVar "B"), Pair (Snd (Var "p"), Fst (Var "p")))

let () =
  printf "%s\n" (string_of_ty (infer_type [] and_comm))

let true_imply_A_imply_A : tm =
  Abs ("f", Impl (True, TVar "A"), App (Var "f", Unit))

let () =
  printf "%s\n" (string_of_ty (infer_type [] true_imply_A_imply_A))

let or_comm : tm =
  Abs ("s", Disj (TVar "A", TVar "B"),
    Case (Var "s", "a", Right (TVar "B", Var "a"),
      "b", Left (Var "b", TVar "A")))

let () =
  printf "%s\n" (string_of_ty (infer_type [] or_comm))

let explosion : tm =
  Abs ("p", Conj (TVar "A", Impl (TVar "A", False)),
    Absurd (App (Snd (Var "p"), Fst (Var "p")), TVar "B"))

let () =
  printf "%s\n" (string_of_ty (infer_type [] explosion))

  let () =
  let l = [
    "A => B";
    "A ⇒ B";
    "A /\\ B";
    "A ∧ B";
    "T";
    "A \\/ B";
    "A ∨ B";
    "_";
    "not A";
    "¬ A";
  ]
  in
  List.iter
    (fun s ->
       Printf.printf
         "the parsing of %S is %s\n%!" s (string_of_ty (ty_of_string s))
    ) l

let () =
  let l = [
    "t u v";
    "fun (x : A) -> t";
    "λ (x : A) → t";
    "(t , u)";
    "fst(t)";
    "snd(t)";
    "()";
    "case t of x -> u | y -> v";
    "left(t,B)";
    "right(A,t)";
    "absurd(t,A)"
  ]
  in
  List.iter
    (fun s ->
       Printf.printf
         "the parsing of %S is %s\n%!" s (string_of_tm (tm_of_string s))
    ) l

let string_of_ctx : context -> string = fun ctx ->
  String.concat " , " (List.map (fun (v, ty) -> sprintf "%s : %s" v (string_of_ty ty)) (List.rev ctx))

let () =
  let ctx = ("Z", True) :: ("x", Impl (TVar "A", TVar "B")) :: ("y", Conj (TVar "A", TVar "B")) :: [] in
  printf "%s\n" (string_of_ctx ctx)

type sequent = context * ty

let string_of_seq : sequent -> string = fun (ctx, ty) ->
    sprintf "%s |- %s" (string_of_ctx ctx) (string_of_ty ty)

let () =
  let seq = (("y", Conj (TVar "A", TVar "B")) :: ("x", Impl (TVar "A", TVar "B")) :: [], TVar "B") in
  printf "%s\n" (string_of_seq seq)

let rec prove env goal =
  print_endline (string_of_seq (env, goal));
  print_string "? "; flush_all ();
  let error e = print_endline e; prove env goal in
  let cmd, arg, name_list =
    let line = input_line stdin in
    let cmd_length = try String.index line ' ' with Not_found -> String.length line in
    let cmd = String.sub line 0 cmd_length in
    let arg_and_name_list = String.sub line cmd_length (String.length line - cmd_length) in
    let arg_and_name_list = String.trim arg_and_name_list in
    let arg_length =
      try String.index arg_and_name_list '[' - 1
      with Not_found -> String.length arg_and_name_list
    in
    let arg =
      if arg_length = -1 then ""
      else String.sub arg_and_name_list 0 arg_length
    in
    let name_list =
      String.sub arg_and_name_list arg_length (String.length arg_and_name_list - arg_length)
    in
    let name_list = String.trim name_list in
    let name_list_length = String.length name_list in
    let name_list =
      if name_list_length >= 2
      then String.sub name_list 1 (name_list_length - 2)
      else name_list
    in
    let name_list =
      List.filter (fun s -> not (String.equal "" s)) (String.split_on_char ' ' name_list)
    in
    cmd, arg, name_list
  in
  let name_list_length = List.length name_list in
  let tactic =
    String.concat " " [ cmd ; arg ] ^
    if name_list_length = 0
    then ""
    else String.concat " " [ " [" ; String.concat " " name_list ; "]" ]
  in
  match cmd with
  | "intro" ->
    begin match goal with
    (* Introduction rule for implication. *)
    | Impl (a, b) ->
      if arg = "" then error "Please provide an argument for intro." else
      let tm, tactics = prove ((arg, a) :: env) b in
      Abs (arg, a, tm), tactic :: tactics
    (* Introduction rule for conjunction. *)
    | Conj (a, b) ->
      let tm1, tactics1 = prove env a in
      let tm2, tactics2 = prove env b in
      Pair (tm1, tm2), List.concat [ [ tactic ] ; tactics1 ; tactics2 ]
    (* Introduction rule for truth. *)
    | True ->
      Unit, [ tactic ]
    | _ ->
      error "Don't know how to introduce this."
    end
  | "zero" ->
    begin match goal with
    (* Introduction rule for nat, corresponding to zero *)
    | Nat ->
      Zero, [ tactic ]
    | _ ->
      error "Don't know how to introduce this."
    end
  | "suc" ->
    begin match goal with
    (* Introduction rule for nat, corresponding to suc *)
    | Nat ->
      let tm, tactics = prove env Nat in
      Suc tm, tactic :: tactics
    | _ ->
      error "Don't know how to introduce this."
    end
  | "elim" ->
    if arg = "" then error "Please provide an argument for elim." else
    begin try
      begin match List.assoc arg env with
      (* Elimination rule for implication. *)
      | Impl (a, b) ->
        if b <> goal
        then error "Argument is of bad type."
        else let tm, tactics = prove env a in
        App (Var arg, tm), tactic :: tactics
      (* Elimination rule for disjunction. *)
      | Disj (a, b) ->
        begin match name_list_length with
        | 0 ->
          let tm1, tactics1 = prove ((arg, a) :: env) goal in
          let tm2, tactics2 = prove ((arg, b) :: env) goal in
          Case (Var arg, arg, tm1, arg, tm2), List.concat [ [ tactic ] ; tactics1 ; tactics2 ]
        | 2 ->
          let v1 = List.nth name_list 0 in
          let v2 = List.nth name_list 1 in
          let tm1, tactics1 = prove ((v1, a) :: env) goal in
          let tm2, tactics2 = prove ((v2, b) :: env) goal in
          Case (Var arg, v1, tm1, v2, tm2), List.concat [ [ tactic ] ; tactics1 ; tactics2 ]
        | _ ->
          error "Bad number of names."
        end
      (* Elimination rule for falsity. *)
      | False ->
        Absurd (Var arg, goal), [ tactic ]
      | Nat ->
        begin match name_list_length with
        | 0 ->
          let tm1, tactics1 = prove env Nat in
          let tm2, tactics2 = prove (("n", Nat) :: ("r", Nat) :: env) Nat in
          Rec (Var arg, tm1, "n", "r", tm2), List.concat [ [ tactic ] ; tactics1 ; tactics2 ]
        | 2 ->
          let v1 = List.nth name_list 0 in
          let v2 = List.nth name_list 1 in
          let tm1, tactics1 = prove env Nat in
          let tm2, tactics2 = prove ((v1, Nat) :: (v2, Nat) :: env) Nat in
          Rec (Var arg, tm1, v1, v2, tm2), List.concat [ [ tactic ] ; tactics1 ; tactics2 ]
        | _ ->
          error "Bad number of names."
        end
      | _ ->
        error "Don't know how to eliminate this."
      end
    with
    | Not_found ->
      error "Argument has to be a variable in context."
    end
  | "cut" ->
    if arg = "" then error "Please provide an argument for cut." else
    begin try
      let arg_ty = ty_of_string arg in
      let tm1, tactics1 = prove env (Impl (arg_ty, goal)) in
      let tm2, tactics2 = prove env arg_ty in
      App (tm1, tm2), List.concat [ [ tactic ] ; tactics1 ; tactics2 ]
    with
    | Failure e ->
      error e
    end
  | "fst" ->
    if arg = "" then error "Please provide an argument for fst." else
    begin try
      match List.assoc arg env with
      | Conj (a, _) when a = goal ->
        Fst (Var arg), [ tactic ]
      | _ ->
        error "Argument is of bad type."
    with
    | Type_error ->
      error "Cannot infer the type of argument."
    | Failure e ->
      error e
    end
  | "snd" ->
    if arg = "" then error "Please provide an argument for snd." else
    begin try
      match List.assoc arg env with
      | Conj (_, b) when b = goal ->
        Snd (Var arg), [ tactic ]
      | _ ->
        error "Argument is of bad type."
    with
    | Type_error ->
      error "Cannot infer the type of argument."
    | Failure e ->
      error e
    end
  | "left" ->
    begin match goal with
    | Disj (a, b) ->
      let tm, tactics = prove env a in
      Left (tm, b), tactic :: tactics
    | _ ->
      error "Argument is of bad type."
    end
  | "right" ->
    begin match goal with
    | Disj (a, b) ->
      let tm, tactics = prove env b in
      Right (a, tm), tactic :: tactics
    | _ ->
      error "Argument is of bad type."
    end
  | "exact" ->
    if arg = "" then error "Please provide an argument for exact." else
    begin try
      let arg_tm = tm_of_string arg in
      if infer_type env arg_tm <> goal
      then error "Argument is of bad type."
      else arg_tm, [ tactic ]
    with
    | Type_error ->
      error "Cannot infer the type of argument."
    | Failure e ->
      error e
    end
  | cmd ->
    error ("Unknown command: " ^ cmd)

let rec main () : unit =
  let error e = print_endline e; main () in
  try
    print_endline "Please enter the formula to prove:";
    let goal = input_line stdin in
    let goal_ty = ty_of_string goal in
    print_endline "Let's prove it.";
    let proof_tm, tactics = prove [] goal_ty in
    print_endline "done.";
    print_endline "Proof term is";
    print_endline (string_of_tm proof_tm);
    print_string  "Typechecking... "; flush_all ();
    assert (infer_type [] proof_tm = goal_ty);
    print_endline "ok.";
    print_endline "Store the proof in a file [y/N]";
    match input_line stdin with
    | "y" ->
      print_endline "Specify the file name:";
      let outfile = open_out ((input_line stdin) ^ ".proof") in
      output_string outfile (String.concat "\n" (goal :: tactics))
    | _ ->
      ()
  with
  | Stdlib.Parsing.Parse_error ->
    error "parsing: error"
  | Failure e ->
    error e
  
let () =
  main ()
