open GT       
open Language

module Util =
  struct

    let stack_of_list list =
      let stack = Stack.create () in
      let _ = List.iter (fun elem -> Stack.push elem stack) (List.rev list) in
      stack

    let list_of_stack stack =
      let list = ref [] in
      let _ = Stack.iter (fun elem -> list := !list @ [elem]) stack in
      !list

  end

(* The type for the stack machine instructions *)
@type insn =
(* binary operator                 *) | BINOP of string
(* put a constant on the stack     *) | CONST of int                 
(* read to stack                   *) | READ
(* write from stack                *) | WRITE
(* load a variable to the stack    *) | LD    of string
(* store a variable from the stack *) | ST    of string
(* a label                         *) | LABEL of string
(* unconditional jump              *) | JMP   of string                                                                                                                
(* conditional jump                *) | CJMP  of string * string
(* begins procedure definition     *) | BEGIN of string list * string list
(* end procedure definition        *) | END
(* calls a procedure               *) | CALL  of string with show
                                                   
(* The type for the stack machine program *)                                                               
type prg = insn list

(* The type for the stack machine configuration: control stack, stack and configuration from statement
   interpreter
 *)
type config = (prg * State.t) list * int list * Stmt.config

(* Stack machine interpreter

     val eval : env -> config -> prg -> config
     
   Takes an environment, a configuration and a program, and returns a configuration as a result. The
   environment is used to locate a label to jump to (via method env#labeled <label_name>)
 *)

type jump_context = Stmt.config * prg
exception JumpException of jump_context;;

let try_eval eval_instruction configuration instruction tail_program =
  try
    ((eval_instruction configuration instruction tail_program), tail_program)
  with JumpException (configuration, program) ->
    (configuration, program)

let rec fold_program eval_instruction configuration program =
  match program with
  | instruction::tail_program ->
    let (configuration, program) = try_eval eval_instruction configuration instruction tail_program in
    fold_program eval_instruction configuration program
  | _ -> configuration

let eval environment (control_stack, stack, configuration) program =
  let control_stack = Util.stack_of_list control_stack in
  let stack = Util.stack_of_list stack in
  let eval_instruction ((state, input, output) as configuration) instruction tail_program =
    match instruction with
    | BINOP op ->
      let lhs = Stack.pop stack in
      let rhs = Stack.pop stack in
      let result = Expr.eval_binop op lhs rhs in
      let _ = Stack.push result stack in
      configuration
    | CONST constant ->
      let _ = Stack.push constant stack in
      configuration
    | READ -> (
      match input with
      | [] -> failwith "Reading empty input"
      | input_head::input ->
        let _ = Stack.push input_head stack in
        (state, input, output)
      )
    | WRITE ->
      let top = Stack.pop stack in
      let output = output @ [top] in
      (state, input, output)
    | LD variable ->
      let value = State.eval state variable in
      let _ = Stack.push value stack in
      configuration
    | ST variable ->
      let value = Stack.pop stack in
      let state = State.update variable value state in
      (state, input, output)
    | LABEL label ->
      configuration
    | JMP label ->
      raise (JumpException (configuration, environment#labeled label))
    | CJMP (test, label) ->
      let top = Stack.pop stack in
      let do_jump = match test with
      | "nz" -> top <> 0
      | "z" -> top = 0
      | _ -> failwith "Unknown CJMP test type"
      in
      let _ = if do_jump then
        raise (JumpException (configuration, environment#labeled label))
      in
      configuration
    | BEGIN (args, locals) ->
      let updater state argument =
        let evaluation = Stack.pop stack in
        State.update argument evaluation state
      in
      let local_state = State.enter state (args @ locals) in
      let local_state = List.fold_left updater local_state args in
      (local_state, input, output)
    | END -> (
      match Stack.is_empty control_stack with
      | true -> configuration
      | false ->
        let (tail_program, old_state) = Stack.pop control_stack in
        let state = State.leave old_state state in
        raise (JumpException ((state, input, output), tail_program))
    )
    | CALL identifier ->
      let _ = Stack.push (tail_program, state) control_stack in
      raise (JumpException (configuration, environment#labeled identifier))
  in
  let configuration = fold_program eval_instruction configuration program in
  let control_stack = Util.list_of_stack control_stack in
  let stack = Util.list_of_stack stack in
  (control_stack, stack, configuration)

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
  let (_, _, (_, _, o)) = eval (object method labeled l = M.find l m end) ([], [], (State.empty, i, [])) p in o

(* Stack machine compiler

     val compile : Language.t -> prg
     
   Takes a program in the source language and returns an equivalent program for the
   stack machine
*)

let make_environment () =
  let label_counter = ref 0 in
  object

    method make_label () =
      let result =".L" ^ string_of_int !label_counter in
      let _ = label_counter := (!label_counter) + 1 in
      result

    method mangle identifier =
      "_Z" ^ identifier

  end

let rec compile_expression expression =
  match expression with
  | Expr.Const constant ->
    [CONST constant]
  | Expr.Var variable ->
    [LD variable]
  | Expr.Binop (op, lhs, rhs) ->
    (compile_expression rhs) @ (compile_expression lhs) @ [BINOP op]

let rec compile_statement environment definitions statement =
  let self = compile_statement environment definitions in
  match statement with
  | Stmt.Read variable ->
    [READ; ST variable]
  | Stmt.Write expression ->
    (compile_expression expression) @ [WRITE]
  | Stmt.Assign (variable, expression) ->
    (compile_expression expression) @ [ST variable]
  | Stmt.Seq (lhs, rhs) ->
    (self lhs) @ (self rhs)
  | Stmt.Skip ->
    []
  | Stmt.If (test, body, otherwise) ->
    let otherwiseLabel = environment#make_label () in
    let endLabel = environment#make_label () in
    let test = compile_expression test in
    let body = self body in
    let otherwise = self otherwise in
    test @ [CJMP ("z", otherwiseLabel)] @ body @ [JMP (endLabel); LABEL (otherwiseLabel)] @ otherwise @ [LABEL (endLabel)]
  | Stmt.While (test, body) ->
    let startLabel = environment#make_label () in
    let endLabel = environment#make_label () in
    let test = compile_expression test in
    let body = self body in
    [LABEL (startLabel)] @ test @ [CJMP ("z", endLabel)] @ body @ [JMP (startLabel); LABEL (endLabel)]
  | Stmt.Repeat (body, test) ->
    let startLabel = environment#make_label () in
    let test = compile_expression test in
    let body = self body in
    [LABEL (startLabel)] @ body @ test @ [CJMP ("z", startLabel)]
  | Stmt.Call (identifier, argument_evaluations) ->
    let argument_evaluations = List.rev argument_evaluations in
    let argument_evaluations = List.concat (List.map compile_expression argument_evaluations) in
    let identifier = environment#mangle identifier in
    argument_evaluations @ [CALL identifier]

let place_definitions environment definitions =
  let place_definition (identifier, (args, locals, body)) =
    let identifier = environment#mangle identifier in
    let body = compile_statement environment definitions body in
    [LABEL identifier; BEGIN (args, locals)] @ body @ [END]
  in
  let defs = List.concat (List.map place_definition definitions) in
  defs

let make_main_identifier () =
  "main"

let make_main body =
  (make_main_identifier (), ([], [], body))

let compile (definitions, statement) =
  let environment = make_environment () in
  let definitions = definitions @ [make_main statement] in
  let program = place_definitions environment definitions in
  let main_label = environment#mangle (make_main_identifier ()) in
  [JMP main_label] @ program
