open GT       
open Language
       
(* The type for the stack machine instructions *)
@type insn =
(* binary operator                 *) | BINOP of string
(* put a constant on the stack     *) | CONST of int                 
(* read to stack                   *) | READ
(* write from stack                *) | WRITE
(* load a variable to the stack    *) | LD    of string
(* store a variable from the stack *) | ST    of string with show

(* The type for the stack machine program *)                                                               
type prg = insn list

(* The type for the stack machine configuration: a stack and a configuration from statement
   interpreter
 *)
type config = int list * Stmt.config

(* Stack machine interpreter
     val eval : config -> prg -> config
   Takes a configuration and a program, and returns a configuration as a result
 *)                         
let rec eval conf prog = 
	match prog with
	| instr::p -> (
		match conf, instr with
		| (y::x::stack, stmt_conf), BINOP operation -> 
			let value = Expr.binop operation x y in
			eval (value::stack, stmt_conf) p
		| (stack, stmt_conf), CONST value ->
			eval (value::stack, stmt_conf) p
		| (stack, (st, z::input, output)), READ ->
			eval (z::stack, (st, input, output)) p
		| (z::stack, (st, input, output)), WRITE ->
			eval (stack, (st, input, output @ [z])) p
		| (stack, (st, input, output)), LD variable ->
			let value = 
				st variable in
			eval (value::stack, (st, input, output)) p
		| (z::stack, (st, input, output)), ST variable ->
			let st' =
				Expr.update variable z st in
			eval (stack, (st', input, output)) p
		| _ -> failwith("Undefined instruction!")
	)
	| [] -> conf

(* Top-level evaluation
     val run : prg -> int list -> int list
   Takes an input stream, a program, and returns an output stream this program calculates
*)
let run p i = let (_, (_, _, o)) = eval ([], (Expr.empty, i, [])) p in o

(* Stack machine compiler
     val compile : Language.Stmt.t -> prg
   Takes a program in the source language and returns an equivalent program for the
   stack machine
 *)
let rec compileExpr expr = 
	match expr with
	| Expr.Const value -> [CONST value]
	| Expr.Var variable -> [LD variable]
	| Expr.Binop (operation, left, right) ->
		compileExpr left @ compileExpr right @ [BINOP operation]

let rec compile stmt = 
	match stmt with
	| Stmt.Assign (variable, expr) -> compileExpr expr @ [ST variable]
	| Stmt.Read variable -> [READ; ST variable]
	| Stmt.Write expr ->	compileExpr expr @ [WRITE]
| Stmt.Seq (left_stmt, right_stmt) -> compile left_stmt @ compile right_stmt
