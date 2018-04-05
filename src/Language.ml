(* Opening a library for generic programming (https://github.com/dboulytchev/GT).
   The library provides "@type ..." syntax extension and plugins like show, etc.
*)
open GT

(* Opening a library for combinator-based syntax analysis *)
open Ostap
open Combinators
open Map
open Set

module Util =
  struct

    let bool_of_int i =
      if i = 0 then false else true

    let int_of_bool b =
      if b then 1 else 0

    let identity x = x

    let rec zip lhs rhs =
      match lhs, rhs with
      | [],_ -> []
      | _, []-> []
      | (x::xs),(y::ys) -> (x,y) :: (zip xs ys)

  end

                         
(* States *)

module StringMap = Map.Make (String)
module StringSet = Set.Make (String)


module State =
  struct

    (* State: global state, local state, scope variables *)
    type table_type = (int) StringMap.t
    type scope_type = StringSet.t

    type t = {globals_table: table_type; locals_table: table_type; scope : scope_type}

    let construct_state globals_table locals_table scope = {
      globals_table = globals_table;
      locals_table = locals_table;
      scope = scope
    }

    (* Empty state *)
    let empty =
      construct_state StringMap.empty StringMap.empty StringSet.empty

    (* Update: non-destructively "modifies" the state s by binding the variable x 
       to value v and returns the new state w.r.t. a scope
    *)
    let update x v s =
        match StringSet.mem x s.scope with
        | true -> { s with locals_table = StringMap.add x v s.locals_table }
        | false -> { s with globals_table = StringMap.add x v s.globals_table }

    (* Evals a variable in a state w.r.t. a scope *)
    let eval s x =
        let table = match StringSet.mem x s.scope with
        | true -> s.locals_table
        | false -> s.globals_table
        in
        StringMap.find x table

    (* Creates a new scope, based on a given state *)
    let enter st xs =
      construct_state st.globals_table StringMap.empty (StringSet.of_list xs)

    (* Drops a scope *)
    let leave st st' =
      construct_state st'.globals_table st.locals_table st.scope

  end
    
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

    let eval_binop op lhs rhs =
      match op with
      | "+" -> lhs + rhs
      | "-" -> lhs - rhs
      | "*" -> lhs * rhs
      | "/" -> lhs / rhs
      | "%" -> lhs mod rhs
      | _ ->
        let result = match op with
        | "==" -> lhs =  rhs
        | "!=" -> lhs != rhs
        | "<=" -> lhs <= rhs
        | "<"  -> lhs <  rhs
        | ">=" -> lhs >= rhs
        | ">"  -> lhs >  rhs
        | _ ->
          let lhs = Util.bool_of_int lhs in
          let rhs = Util.bool_of_int rhs in
          match op with
          | "!!" -> lhs || rhs
          | "&&" -> lhs && rhs
          | _ -> failwith (Printf.sprintf "Unwanted operation '%s'" op) in
        Util.int_of_bool result

    (* Expression evaluator
    
          val eval : state -> t -> int
 
       Takes a state and an expression, and returns the value of the expression in 
       the given state.
    *)                                                       
    let rec eval state expression =
      let self = eval state in
      match expression with
      | Const constant -> constant
      | Var variable -> State.eval state variable
      | Binop(op, lhs, rhs) ->
        let lhs = self lhs in
        let rhs = self rhs in
        eval_binop op lhs rhs

    (* Expression parser. You can use the following terminals:
    
         IDENT   --- a non-empty identifier a-zA-Z[a-zA-Z0-9_]* as a string
         DECIMAL --- a decimal constant [0-9]+ as a string
                                                                                                                  
    *)

    let ostap_ops_of_binops ops =
      let mapper op =
        (ostap ($(op)), (fun lhs rhs -> Binop (op, lhs, rhs) ))
        in
      List.map mapper ops

    ostap (
      parse:
        !(Ostap.Util.expr
         (Util.identity)
         [|
           `Lefta, ostap_ops_of_binops ["!!"];
           `Lefta, ostap_ops_of_binops ["&&"];
           `Nona,  ostap_ops_of_binops ["<="; ">="; "<"; ">"; "=="; "!="];
           `Lefta, ostap_ops_of_binops ["+"; "-"];
           `Lefta, ostap_ops_of_binops ["*"; "/"; "%"]
         |]
         root_rule
        );

      variable_rule:
        variable:IDENT { Var (variable) };

      constant_rule:
        constant:DECIMAL { Const (constant) };

      root_rule:
          variable_rule
        | constant_rule
        | -"(" parse -")"
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
    (* composition                      *) | Seq    of t * t 
    (* empty statement                  *) | Skip
    (* conditional                      *) | If     of Expr.t * t * t
    (* loop with a pre-condition        *) | While  of Expr.t * t
    (* loop with a post-condition       *) | Repeat of t * Expr.t
    (* call a procedure                 *) | Call   of string * Expr.t list with show
                                                                    
    (* The type of configuration: a state, an input stream, an output stream *)
    type config = State.t * int list * int list 

    (* Statement evaluator
    
         val eval : env -> config -> t -> config
         
       Takes an environment, a configuration and a statement, and returns another configuration. The 
       environment supplies the following method
       
           method definition : string -> (string list, string list, t)
           
       which returns a list of formal parameters, local variables, and a body for given definition
    *)
    let rec whileImpl eval test body configuration =
      let self = whileImpl eval test body in
      let (state, _, _) = configuration in
      match Expr.eval state test with
      | 0 -> configuration
      | _ -> self (eval configuration body)

    let rec repeatImpl eval test body configuration =
      let self = repeatImpl eval test body in
      let (state, _, _) = configuration in
      match Expr.eval state test with
      | 0 -> self (eval configuration body)
      | _ -> configuration

    let rec eval environment configuration statement =
      let self = eval environment in
      let (state, input, output) = configuration in
      match statement with
      | Read variable -> (
        match input with
          | [] -> failwith "Reading empty input"
          | input_head::input ->
            let state = State.update variable input_head state in
            (state, input, output)
        )
      | Write expression ->
        let result = Expr.eval state expression in
        let output = output @ [result] in
        (state, input, output)
      | Assign (variable, expression) ->
        let result = Expr.eval state expression in
        let state = State.update variable result state in
        (state, input, output)
      | Seq (lhs, rhs) ->
        self (self configuration lhs) rhs
      | Skip ->
        configuration
      | If (test, body, otherwise) -> (
        match (Expr.eval state test) with
        | 0 -> self configuration otherwise
        | _ -> self configuration body
        )
      | While (test, body) ->
        whileImpl self test body configuration
      | Repeat (body, test) ->
        repeatImpl self test body (self configuration body)
      | Call (identifier, argument_evaluations) ->
        let (args, locals, body) = environment#find_definition identifier in
        let argument_evaluations = List.map (Expr.eval state) argument_evaluations in
        let argument_assignments = Util.zip args argument_evaluations in
        let updater state (argument, evaluation) =
          State.update argument evaluation state
        in

        let local_state = State.enter state (args @ locals) in
        let local_state = List.fold_left updater local_state argument_assignments in
        let (local_state, input, output) = self (local_state, input, output) body in
        let state = State.leave state local_state in
        (state, input, output)


    let rec parseElif elifList elseBody =
      match elifList with
      | [] -> elseBody
      | (condition, body)::tail ->
        If (condition, body, parseElif tail elseBody)

    let parseElse elifList elseBody =
      let elseBody = match elseBody with
      | None -> Skip
      | Some body -> body
      in
      parseElif elifList elseBody

    (* Statement parser *)
    ostap(
      parse:
          sequence_rule
        | statement_rule;

      statement_rule:
          read_rule
        | write_rule
        | assignment_rule
        | skip_rule
        | if_rule
        | while_rule
        | repeat_rule
        | for_rule
        | call_rule;

      read_rule:
        "read" -"(" variable:IDENT -")"
        { Read (variable) };

      write_rule:
        "write" -"(" expression:!(Expr.parse) -")"
        { Write (expression) };

      assignment_rule:
        variable:IDENT -":=" expression:!(Expr.parse)
        { Assign (variable, expression) };

      sequence_rule:
        lhs:statement_rule -";" rhs:parse
        { Seq (lhs, rhs) };

      skip_rule:
        %"skip"
        {Skip};

      if_rule:
        %"if" test:!(Expr.parse)
        %"then" thenBody:parse
        elifBodies:(%"elif"!(Expr.parse) %"then" parse)*
        elseBody:(%"else" parse)?
        %"fi"
        { If (test, thenBody, parseElse elifBodies elseBody) };

      while_rule:
        %"while" test:!(Expr.parse)
        %"do" body:parse
        %"od"
        { While (test, body) };

      repeat_rule:
        %"repeat" body:parse
        %"until" test:!(Expr.parse)
        { Repeat (body, test) };

      for_rule:
        %"for" init:parse "," test:!(Expr.parse) "," iteration:parse
        %"do" body:parse
        %"od"
        { Seq(init, While (test, Seq (body, iteration))) };

      call_rule:
        identifier:IDENT "(" args:(argument_evaluation_rule | empty_rule) ")"
        { Call(identifier, args) };

      argument_evaluation_rule:
        head:!(Expr.parse) tail:((-"," !(Expr.parse))* )
        { head::tail };

      empty_rule:
        empty
        { [] }
    )

  end

(* Function and procedure definitions *)
module Definition =
  struct

    (* The type for a definition: name, argument list, local variables, body *)
    type t = string * (string list * string list * Stmt.t)

    ostap (
      parse:
        %"fun" identifier:IDENT
        "(" args:(identifier_list_rule | empty_rule) ")"
        locals:(-(%"local") identifier_list_rule | empty_rule)
        "{" body:body_rule "}"
        { identifier, (args, locals, body) };

      body_rule:
        !(Stmt.parse);

      empty_rule:
        empty
        { [] };

      identifier_list_rule:
        head:IDENT tail:((-"," IDENT)* )
        { head :: tail }
    )

  end
    
(* The top-level definitions *)

(* The top-level syntax category is a pair of definition list and statement (program body) *)
type t = Definition.t list * Stmt.t    

(* Top-level evaluator

     eval : t -> int list -> int list
     
   Takes a program and its input stream, and returns the output stream
*)

let make_environment definitions =
  let definitions = List.fold_left (fun map (key, value) -> StringMap.add key value map) StringMap.empty definitions in
  object
    method find_definition key =
      StringMap.find key definitions
  end

let eval (definitions, program) input_stream =
  let environment = make_environment definitions in
  let _, _, output_stream = Stmt.eval environment (State.empty, input_stream, []) program in
  output_stream

(* Top-level parser *)
let parse = ostap (!(Definition.parse)* !(Stmt.parse))
