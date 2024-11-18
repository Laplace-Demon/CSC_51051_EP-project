(** Type variables. *)
type tvar = string

(** Term variables. *)
type var = string

(** Types. *)
type ty =
  | TVar of tvar
  | Impl of ty * ty
  | Conj of ty * ty
  | Disj of ty * ty
  | True
  | False

type tm =
  | Var of var
  | App of tm * tm
  | Abs of var * ty * tm
  (* Conjunction. *)
  | Pair of tm * tm
  | Fst of tm
  | Snd of tm
  (* Disjunction. *)
  | Left of tm * ty
  | Right of ty * tm
  | Case of tm * var * tm * var * tm
  (* Truth. *)
  | Unit
  (* Falsity. *)
  | Absurd of tm * ty
