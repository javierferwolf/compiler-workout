(* Opening a library for generic programming (https://github.com/dboulytchev/GT).
   The library provides "@type ..." syntax extension and plugins like show, etc.
*)
open GT

(* Opening a library for combinator-based syntax analysis *)
open Ostap.Combinators
open Ostap
open List
       
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
    let int_to_bool x = x != 0
    let bool_to_int x = if x then 1 else 0
    
    let rec eval st expr = match expr with
        | Const n -> n
        | Var x -> st x
        | Binop (op, x, y) -> 
            let x = eval st x in 
            let y = eval st y in
            match op with 
                | "!!" -> bool_to_int (int_to_bool x || int_to_bool y)
                | "&&" -> bool_to_int (int_to_bool x && int_to_bool y)
                | "==" -> bool_to_int (x == y)
                | "!=" -> bool_to_int (x != y)
                | "<=" -> bool_to_int (x <= y)
                | "<" -> bool_to_int (x < y)
                | ">=" -> bool_to_int (x >= y)
                | ">" -> bool_to_int (x > y)
                | "+" -> x + y
                | "-" -> x - y
                | "*" -> x * y
                | "/" -> x / y
                | "%" -> x mod y
                | _ -> failwith "Wrong operation"

    (* Expression parser. You can use the following terminals:
         IDENT   --- a non-empty identifier a-zA-Z[a-zA-Z0-9_]* as a string
         DECIMAL --- a decimal constant [0-9]+ as a string
   
    *)

    let specifiers lst = map (fun op -> (ostap ($(op)), fun x y -> Binop (op, x, y))) lst

    ostap (
      parse: expr;
      expr: 
        !(Util.expr
            (fun x -> x)
            [|
              `Lefta, specifiers ["!!"];
              `Lefta, specifiers ["&&"];
              `Nona, specifiers ["<="; ">="; "<"; ">"; "=="; "!="];
              `Lefta, specifiers ["+"; "-"];
              `Lefta, specifiers ["*"; "/"; "%"]
            |]
            primary
        );

      primary: x:IDENT {Var x} | n:DECIMAL {Const n} | -"(" expr -")"
    )

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
    let rec eval (state, input, output) stmt = match stmt with
        | Read var -> (Expr.update var (hd input) state, tl input, output)
        | Write expr -> (state, input, output @ [Expr.eval state expr])
        | Assign (var, expr) -> (Expr.update var (Expr.eval state expr) state, input, output)
        | Seq (s1, s2) -> eval (eval (state, input, output) s1) s2 

    (* Statement parser *)
    ostap (
      parse: statements;
      statements: <s::ss> : !(Util.listBy)[ostap (";")][stmt] {List.fold_left (fun a b -> Seq (a, b)) s ss};
      stmt: 
        x:IDENT ":=" e:!(Expr.parse) {Assign (x, e)}
        | "write" "(" e:!(Expr.parse) ")" {Write e}
        | "read" "(" x:IDENT ")" {Read x}

    )
      
  end

(* The top-level definitions *)

(* The top-level syntax category is statement *)
type t = Stmt.t    

(* Top-level evaluator
     eval : t -> int list -> int list
   Takes a program and its input stream, and returns the output stream
*)
let eval p i =
  let _, _, o = Stmt.eval (Expr.empty, i, []) p in o

