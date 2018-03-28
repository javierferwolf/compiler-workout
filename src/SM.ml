open GT       
       
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
type config = int list * Syntax.Stmt.config

(* Stack machine interpreter

     val eval : config -> prg -> config

   Takes a configuration and a program, and returns a configuration as a result
 *)                         
let rec eval (stack, (s, i, o)) p =
 	  if (List.length p)=0 then (stack, (s, i, o))
 	  else eval
 	  (match (List.hd p) with
 	    BINOP op -> (match stack with first::second::rest ->
 		     ((Syntax.Expr.eval s (Syntax.Expr.Binop op (Syntax.Expr.Const second) (Syntax.Expr.Const first)))::rest, (s, i, o)))
 	    |CONST x -> (x::stack, (s, i, o))
 	    |READ -> ((List.hd i)::stack, (s, List.tl i, o))
 	    |WRITE -> (match stack with first::rest -> (rest, (s, i, o @ [first])))
 	    |LD x -> ((s x)::stack, (s, i, o))
 	    |ST x -> (match stack with first::rest -> (rest, (Syntax.Expr.update x first s, i, o)))
 	   ) (List.tl p);;

(* Top-level evaluation
     val run : int list -> prg -> int list
   Takes an input stream, a program, and returns an output stream this program calculates
*)
let run i p = let (_, (_, _, o)) = eval ([], (Syntax.Expr.empty, i, [])) p in o

(* Stack machine compiler
     val compile : Syntax.Stmt.t -> prg
   Takes a program in the source language and returns an equivalent program for the
   stack machine
 *)

 let rec compile stmt =
 	let rec compile_exp exp =
match exp with
         	Syntax.Expr.Const c -> [CONST c]
          |Syntax.Expr.Var v -> [LD v]
        	|Syntax.Expr.Binop(op, l, r) -> (compile_exp l) @ (compile_exp r) @ [BINOP op]
 	in
 	match stmt with
 	  Syntax.Stmt.Read x -> [READ; ST x]
 	  |Syntax.Stmt.Write exp -> (compile_exp exp) @ [WRITE]
 	  |Syntax.Stmt.Assign(x, exp) -> (compile_exp exp) @ [ST x]
         |Syntax.Stmt.Seq(l, r) -> (compile l) @ (compile r) ;;
