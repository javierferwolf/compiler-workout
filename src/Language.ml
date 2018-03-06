(* Opening a library for generic programming (https://github.com/dboulytchev/GT).
   The library provides "@type ..." syntax extension and plugins like show, etc.
*)
open GT

(* Opening a library for combinator-based syntax analysis *)
open Ostap.Combinators
       
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
    
    let int_to_bool value = 
	    if value == 0 then false else true
    let bool_to_int value = 
	    if value then 1 else 0

    let binop operation left_operand right_operand = 
	    match operation with
	    | "+"   -> left_operand + right_operand
	    | "-"   -> left_operand - right_operand
	    | "*"   -> left_operand * right_operand
	    | "/"   -> left_operand / right_operand
	    | "%"   -> left_operand mod right_operand
	    | "&&"  -> bool_to_int (int_to_bool left_operand && int_to_bool right_operand)
	    | "!!"  -> bool_to_int (int_to_bool left_operand || int_to_bool right_operand)
	    | "<" -> bool_to_int (left_operand < right_operand)
	    | "<="  -> bool_to_int (left_operand <= right_operand)
	    | ">" -> bool_to_int (left_operand > right_operand)
	    | ">="  -> bool_to_int (left_operand >= right_operand)
	    | "=="  -> bool_to_int (left_operand == right_operand)
	    | "!="  -> bool_to_int (left_operand != right_operand)
	    | _ -> failwith("Undefined operator!")

    let rec eval st expr = 
    	match expr with
		| Const const -> const
		| Var variable -> st variable
		| Binop (operation, left, right) ->
		  let left_operand = 
		    eval st left in
		  let right_operand = 
		    eval st right in
		  binop operation left_operand right_operand

    (* Expression parser. You can use the following terminals:

         IDENT   --- a non-empty identifier a-zA-Z[a-zA-Z0-9_]* as a string
         DECIMAL --- a decimal constant [0-9]+ as a string
   
    *)
     let mapoperation operations = List.map (fun operation -> ostap($(operation)), (fun left right -> Binop (operation, left, right))) operations

    ostap (
      parse: empty {failwith "Not implemented yet"}
   parse: 
    		!(Ostap.Util.expr
    			(fun x -> x)
    			[|
    				`Lefta, mapoperation ["!!"];
	   				`Lefta, mapoperation ["&&"];
    				`Nona,  mapoperation ["=="; "!=";">="; ">"; "<="; "<"];
    				`Lefta, mapoperation ["+"; "-"];
    				`Lefta, mapoperation ["*"; "/"; "%"];
    			|]
    			primary
    		);
    	primary: variable:IDENT {Var variable} | const:DECIMAL {Const const} | -"(" parse -")"
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
    let eval _ = failwith "Not implemented yet"

let rec eval conf stmt =
    	match conf, stmt with
    	| (st, input, output) , Assign (variable, expr) -> 
    		let value = 
    			Expr.eval st expr in
    		(Expr.update variable value st, input, output)
    	| (st, z::input, output), Read variable ->
    		(Expr.update variable z st, input, output)
    	| (st, input, output), Write expr ->
    		let value = 
    			Expr.eval st expr in
    		(st, input, output @ [value])
    	| conf, Seq (left_stmt, right_stmt) ->
    		eval (eval conf left_stmt) right_stmt
    	| _, _ -> failwith("Undefined statement!")

(* Statement parser *)
    ostap (
      parse: empty {failwith "Not implemented yet"}
      parse: seq | stmt;
      stmt: assign | read | write;
      assign: variable:IDENT -":=" expr:!(Expr.parse) {Assign (variable, expr)};
      read: -"read" -"(" variable:IDENT -")" {Read variable};
      write: -"write" -"(" expr:!(Expr.parse) -")" {Write expr};
      seq: left_stmt:stmt -";" right_stmt:parse {Seq (left_stmt, right_stmt)}
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

(* Top-level parser *)
let parse = Stmt.parse                                                     
