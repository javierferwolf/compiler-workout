open GT       
open Language
       
(* The type for the stack machine instructions *)
@type insn =
(* binary operator                 *) | BINOP   of string
(* put a constant on the stack     *) | CONST   of int
(* put a string on the stack       *) | STRING  of string                      
(* load a variable to the stack    *) | LD      of string
(* store a variable from the stack *) | ST      of string
(* store in an array               *) | STA     of string * int
(* a label                         *) | LABEL   of string
(* unconditional jump              *) | JMP     of string
(* conditional jump                *) | CJMP    of string * string
(* begins procedure definition     *) | BEGIN   of string * string list * string list
(* end procedure definition        *) | END
(* calls a function/procedure      *) | CALL    of string * int * bool
(* returns from a function         *) | RET     of bool with show
                                                   
(* The type for the stack machine program *)
type prg = insn list
                            
(* The type for the stack machine configuration: control stack, stack and configuration from statement
   interpreter
*)
type config = (prg * State.t) list * Value.t list * Expr.config

(* Stack machine interpreter

     val eval : env -> config -> prg -> config
     
   Takes an environment, a configuration and a program, and returns a configuration as a result. The
   environment is used to locate a label to jump to (via method env#labeled <label_name>)
*)
let split n l =
  let rec unzip (taken, rest) = function
  | 0 -> (List.rev taken, rest)
  | n -> let h::tl = rest in unzip (h::taken, tl) (n-1)
  in
  unzip ([], l) n
        
let rec eval env config prg = 
	match prg with 
	| [] -> config
	| insn::p ->
		match config, insn with
		| (cstack, y::x::stack, c), BINOP operators -> 
	eval env (cstack, (Value.of_int (Expr.comp operators (Value.to_int x) (Value.to_int y)))::stack, c) p
	 	| (cstack, stack, (s, i, o)), LD x -> eval env (cstack, (State.eval s x)::stack, (s, i, o)) p
		| (cstack, stack, conf), CONST value -> eval env (cstack, (Value.of_int value) :: stack, conf) p
		| (cstack, z::stack, (s, i, o)), ST x -> eval env (cstack, stack, ((Language.State.update x z s), i, o)) p
		| (cstack, stack, c), STRING str ->
                  eval env (cstack, (Value.of_string str)::stack, c) p
		|(cstack, stack, (s, i, o)), STA (x, n) -> 
      let v::ind, stack' = split (n + 1) stack in 
      eval env (cstack, stack', (Language.Stmt.update s x v (List.rev ind), i, o)) p
		| (cstack, stack, (s, i, o)), CALL (func, n, fl) -> if env#is_label func then eval env ((p, s)::cstack, stack, (s, i, o)) (env#labeled func) else eval env (env#builtin config func n fl) p
		| config, LABEL _ -> eval env config p
		| config, JMP label -> eval env config (env#labeled label)
    		| (cstack, z::stack, c), CJMP (cond, label)  -> (
		let x = match cond with
		| "nz" ->  Value.to_int z <> 0
		| "z" ->  Value.to_int z = 0 
	      	in eval env (cstack, stack, c) (if (x) then (env#labeled label) else p)
		)
		| (cstack, stack, (s, i, o)), BEGIN (_, args, x) ->
      		  let rec getArgs s = function
       			| a::args, z::stack -> let s', stack' = getArgs s (args, stack)
        		in State.update a z s', stack'
        		| [], stack -> s, stack
      		  in let s', stack' = getArgs (State.enter s (args @ x)) (args, stack)
      		  in eval env (cstack, stack', (s', i, o)) p
   		| (cstack, stack, (s, i, o)), END | (cstack, stack, (s, i, o)), RET _ ->
		(
      		  match cstack with
      		  | (prg, s')::cstack' ->
       		    eval env (cstack', stack, (State.leave s s', i, o)) prg
      		  | [] -> config
                )

(* Top-level evaluation

     val run : prg -> int list -> int list
     
   Takes a program, an input stream, and returns an output stream this program calculates
*)
let run p i =
  let module M = Map.Make (String) in
  let rec make_map m = function
  | []              -> m
  | (LABEL l) :: tl -> make_map (M.add l tl m) tl
  | _ :: tl         -> make_map m tl
  in
  let m = make_map M.empty p in
  let (_, _, (_, _, o)) =
    eval
      (object
         method is_label l = M.mem l m
         method labeled l = M.find l m
         method builtin (cstack, stack, (st, i, o)) f n p =
           let f = match f.[0] with 'L' -> String.sub f 1 (String.length f - 1) | _ -> f in
           let args, stack' = split n stack in
           let (st, i, o, r) = Language.Builtin.eval (st, i, o, None) (List.rev args) f in
           let stack'' = if p then stack' else let Some r = r in r::stack' in
           Printf.printf "Builtin: %s\n";
           (cstack, stack'', (st, i, o))
       end
      )
      ([], [], (State.empty, i, []))
      p
  in
  o

(* Stack machine compiler

     val compile : Language.t -> prg
     
   Takes a program in the source language and returns an equivalent program for the
   stack machine
*)
let rec compileExpr expr = 
	match expr with
	| Expr.Const c -> [CONST c]
	| Expr.Var x -> [LD x]
	| Expr.String s -> [STRING s]
	| Expr.Array elems -> List.flatten (List.map compileExpr elems) @ [CALL ("$array", List.length elems, false)]
	| Expr.Elem (elems, i) ->  compileExpr elems @ compileExpr i @ [CALL ("$elem", 2, false)]
        | Expr.Length e -> compileExpr e @ [CALL ("$length", 1, false)];
	| Expr.Binop (op, first, second) -> compileExpr first @ compileExpr second @ [BINOP op]
	| Expr.Call (name, params) -> List.concat (List.map compileExpr (List.rev params)) @ [CALL ("L" ^ name, List.length params, false)]

let env = object 
val mutable id = 0
    method gen = 
    id <- (id + 1);
    "L" ^ string_of_int id
end

let compile (defs, stmt) = 
    let rec compileStmt stmt =
	match stmt with
	| Stmt.Assign (x, [], e) -> compileExpr e @ [ST x]
	| Stmt.Assign (x, ind, e) -> List.flatten (List.map compileExpr (ind @ [e])) @ [STA (x, List.length ind)]
	| Stmt.Seq (firstStmt, secondStmt) -> (compileStmt firstStmt) @ (compileStmt secondStmt)
	| Stmt.Skip -> []
  	| Stmt.If (e, t, f) ->
    	let elseLabel = env#gen in
    	let endLabel = env#gen in
    	let curCase = compileStmt t in
    	let lastCase = compileStmt f in
    		(compileExpr e @ [CJMP ("z", elseLabel)] @ curCase @ [JMP endLabel] @ [LABEL elseLabel] @ lastCase @ [LABEL endLabel])
  	| Stmt.While (e, s) ->
   	let condLabel = env#gen in
    	let loopLabel = env#gen in
    	let body = compileStmt s in
    		([JMP condLabel] @ [LABEL loopLabel] @ body @ [LABEL condLabel] @ compileExpr e @ [CJMP ("nz", loopLabel)])
  	| Stmt.Repeat (e, s) ->
    	let loopLabel = env#gen in
    	let body = compileStmt s in
    		([LABEL loopLabel] @ body @ compileExpr e @ [CJMP ("z", loopLabel)])
	| Stmt.Call (name, p) -> 
	    List.concat (List.map compileExpr p) @ [CALL ("L" ^ name, List.length p, true)] 
	|Stmt.Return expr -> (
      	    match expr with
            | None -> [RET false]
            | Some expr -> compileExpr expr @ [RET true]
        )
	| _ -> failwith "Undefined"
	in
	let compile_def (fun_name, (args, locals, body)) =
	  [LABEL ("L" ^ fun_name); BEGIN (fun_name, args, locals)] @ compileStmt body @ [END]
	  in
	  compileStmt stmt @ [END] @ List.concat (List.map compile_def defs)
