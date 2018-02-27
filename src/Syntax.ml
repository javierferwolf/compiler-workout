(* Opening a library for generic programming (https://github.com/dboulytchev/GT).
   The library provides "@type ..." syntax extension and plugins like show, etc.
*)
open GT 
    
(* Simple expressions: syntax and semantics *)
module Expr =
  struct
    
    (* The type for expressions. Note, in regular OCaml there is no "@type..." 
       notation, it came from GT. 
    *)
    @type t =
    (* integer constant *) | Const of int
    (* variable         *) | Var   of string
    (* binary operator  *) | Binop of string * t * t with show

    (* Available binary operators:
        !!                   --- disjunction
        &&                   --- conjunction
        ==, !=, <=, <, >=, > --- comparisons
        +, -                 --- addition, subtraction
        *, /, %              --- multiplication, division, reminder
    *)
                                                            
    (* State: a partial map from variables to integer values. *)
    type state = string -> int 

    (* Empty state: maps every variable into nothing. *)
    let empty = fun x -> failwith (Printf.sprintf "Undefined variable %s" x)

    (* Update: non-destructively "modifies" the state s by binding the variable x 
      to value v and returns the new state.
    *)
    let update x v s = fun y -> if x = y then v else s y

    (* Expression evaluator

          val eval : state -> t -> int
 
       Takes a state and an expression, and returns the value of the expression in 
       the given state.
    *)
    let eval _ = failwith "Not implemented yet"
    
let rec eval s exp =
	match exp with
         Const c -> c
         | Var v -> s v
         | Binop("+", l, r) -> eval s l + eval s r
         | Binop("-", l, r) -> eval s l - eval s r
         | Binop("*", l, r) -> eval s l * eval s r
	 | Binop("/", l, r) -> eval s l / eval s r
         | Binop("%", l, r) -> eval s l mod eval s r
         | Binop("<", l, r) -> if eval s l < eval s r then 1 else 0
         | Binop("<=", l, r) -> if eval s l <= eval s r then 1 else 0
         | Binop(">", l, r) -> if eval s l > eval s r then 1 else 0
         | Binop(">=", l, r) -> if eval s l >= eval s r then 1 else 0
         | Binop("==", l, r) -> if eval s l = eval s r then 1 else 0
         | Binop("!=", l, r) -> if eval s l <> eval s r then 1 else 0
         | Binop("!!", l, r) -> if (if eval s l = 0 then false else  true) || (if eval s r = 0 then false else true) then 1 else 0
         | Binop("&&", l, r) -> if (if eval s l = 0 then false else true) && (if eval s r = 0 then false else true) then 1 else 0;;
  end
                    
(* Simple statements: syntax and sematics *)
module Stmt =
  struct

    (* The type for statements *)
    @type t =
    (* read into the variable           *) | Read   of string
    (* write the value of an expression *) | Write  of Expr.t
    (* assignment                       *) | Assign of string * Expr.t
    (* composition                      *) | Seq    of t * t with show

    (* The type of configuration: a state, an input stream, an output stream *)
    type config = Expr.state * int list * int list 

    (* Statement evaluator

          val eval : config -> t -> config

       Takes a configuration and a statement, and returns another configuration
    *)
    let eval _ = failwith "Not implemented yet"
let rec eval (s, i, o) stmt = 
        match stmt with
	Read x -> (Expr.update x (List.hd i) s, List.tl i, o)
	|Write exp -> (s, i, o @ [Expr.eval s exp])
	|Assign(x, exp) -> (Expr.update x (Expr.eval s exp) s, i, o)
	|Seq(l, r) -> eval (eval (s, i, o) l) r;;  
                                                         
  end
