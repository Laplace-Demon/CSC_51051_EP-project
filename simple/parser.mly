%{
open Expr
%}

%token IMP AND OR TRUE FALSE NAT NOT
%token FUN TO CASE OF
%token LPAR RPAR COLON COMMA BAR
%token FST SND LEFT RIGHT ABSURD ZERO SUC REC
%token <string> IDENT
%token EOF

%right IMP
%right OR
%right AND
%nonassoc NOT

%start ty
%start tm
%type <Expr.ty> ty
%type <Expr.tm> tm
%%

/* A type */
ty:
  | IDENT        { TVar $1 }
  | LPAR ty RPAR { $2 }
  | ty IMP ty    { Impl ($1, $3) }
  | ty AND ty    { Conj ($1, $3) }
  | ty OR ty     { Disj ($1, $3) }
  | NOT ty       { Impl ($2, False) }
  | TRUE         { True }
  | FALSE        { False }
  | NAT          { Nat }

/* A term */
tm:
  | atm                                    { $1 }
  | FUN LPAR IDENT COLON ty RPAR TO tm     { Abs ($3, $5, $8) }
  | CASE tm OF IDENT TO tm BAR IDENT TO tm { Case ($2, $4, $6, $8, $10) }

/* An application */
atm:
  | stm     { $1 }
  | atm stm { App ($1, $2) }

/* A simple term */
stm:
  | IDENT                                                      { Var $1 }
  | LPAR tm RPAR                                               { $2 }
  | FST stm                                                    { Fst $2 }
  | SND stm                                                    { Snd $2 }
  | LPAR RPAR                                                  { Unit }
  | LPAR tm COMMA tm RPAR                                      { Pair ($2, $4) }
  | LEFT LPAR tm COMMA ty RPAR                                 { Left ($3, $5) }
  | RIGHT LPAR ty COMMA tm RPAR                                { Right ($3, $5) }
  | ABSURD LPAR tm COMMA ty RPAR                               { Absurd ($3, $5) }
  | ZERO                                                       { Zero }
  | SUC stm                                                    { Suc $2 }
  | REC LPAR tm COMMA tm COMMA IDENT COMMA IDENT COMMA tm RPAR { Rec ($3, $5, $7, $9, $11) }
