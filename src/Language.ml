(* Opening a library for generic programming (https://github.com/dboulytchev/GT).
   The library provides "@type ..." syntax extension and plugins like show, etc.
*)
open GT

(* Opening a library for combinator-based syntax analysis *)
open Ostap
open Combinators
open List 
(* Values *)
module Value =
  struct

    @type t = Int of int | String of string | Array of t list with show

    let to_int = function 
    | Int n -> n 
    | _ -> failwith "int value expected"

    let to_string = function 
    | String s -> s 
    | _ -> failwith "string value expected"

    let to_array = function
    | Array a -> a
    | _       -> failwith "array value expected"

    let of_int    n = Int    n
    let of_string s = String s
    let of_array  a = Array  a

    let update_string s i x = String.init (String.length s) (fun j -> if j = i then x else s.[j])
    let listInit n f =
        let rec init i n f =
          if i >= n then []
          else (f i) :: (init (i + 1) n f)
        in init 0 n f

    let update_array  a i x = listInit   (List.length a)   (fun j -> if j = i then x else List.nth a j)
  end
       
(* States *)
module State =
  struct
                                                                
    (* State: global state, local state, scope variables *)
    type t = {g : string -> Value.t; l : string -> Value.t; scope : string list}

    (* Empty state *)
    let empty =
      let e x = failwith (Printf.sprintf "Undefined variable: %s" x) in
      {g = e; l = e; scope = []}

    (* Update: non-destructively "modifies" the state s by binding the variable x 
       to value v and returns the new state w.r.t. a scope
    *)
    let update x v s =
      let u x v s = fun y -> if x = y then v else s y in
      if List.mem x s.scope then {s with l = u x v s.l} else {s with g = u x v s.g}

    (* Evals a variable in a state w.r.t. a scope *)
    let eval s x = (if List.mem x s.scope then s.l else s.g) x

    (* Creates a new scope, based on a given state *)
    let enter st xs = {empty with g = st.g; scope = xs}

    (* Drops a scope *)
    let leave st st' = {st' with g = st.g}

  end

(* Builtins *)
module Builtin =
  struct

    let eval (st, i, o, _) args = function
    | "read"     -> (match i with z::i' -> (st, i', o, Some (Value.of_int z)) | _ -> failwith "Unexpected end of input")
    | "write"    -> (st, i, o @ [Value.to_int @@ List.hd args], None)
    | "$elem"    -> let [b; j] = args in
                    (st, i, o, let i = Value.to_int j in
                               Some (match b with
                                     | Value.String s -> Value.of_int @@ Char.code s.[i]
                                     | Value.Array  a -> List.nth a i
                               )
                    )         
    | "$length"  -> (st, i, o, Some (Value.of_int (match List.hd args with Value.Array a -> List.length a | Value.String s -> String.length s)))
    | "$array"   -> (st, i, o, Some (Value.of_array args))
    | "isArray"  -> let [a] = args in (st, i, o, Some (Value.of_int @@ match a with Value.Array  _ -> 1 | _ -> 0))
    | "isString" -> let [a] = args in (st, i, o, Some (Value.of_int @@ match a with Value.String _ -> 1 | _ -> 0))                     
       
  end
    
(* Simple expressions: syntax and semantics *)
module Expr =
  struct
    
    (* The type for expressions. Note, in regular OCaml there is no "@type..." 
       notation, it came from GT. 
    *)
    @type t =
    (* integer constant   *) | Const  of int
    (* array              *) | Array  of t list
    (* string             *) | String of string
    (* S-expressions      *) | Sexp   of string * t list
    (* variable           *) | Var    of string
    (* binary operator    *) | Binop  of string * t * t
    (* element extraction *) | Elem   of t * t
    (* length             *) | Length of t 
    (* function call      *) | Call   of string * t list with show

    (* Available binary operators:
        !!                   --- disjunction
        &&                   --- conjunction
        ==, !=, <=, <, >=, > --- comparisons
        +, -                 --- addition, subtraction
        *, /, %              --- multiplication, division, reminder
    *)

    (* The type of configuration: a state, an input stream, an output stream, an optional value *)
    type config = State.t * int list * int list * Value.t option
                                                            
    (* Expression evaluator
    
          val eval : env -> config -> t -> int * config
          
          
       Takes an environment, a configuration and an expresion, and returns another configuration. The 
       environment supplies the following method
       
           method definition : env -> string -> int list -> config -> config
           
       which takes an environment (of the same type), a name of the function, a list of actual parameters and a configuration, 
       an returns a pair: the return value for the call and the resulting configuration
    *)                                                       
    let comp operators right left =
    let numericbool numbers = if numbers != 0 then true else false in 
    let boolnumeric numbers = if numbers then 1 else 0 in
    match operators with
    |"+" -> (right + left)
    |"-" -> (right - left)
    |"*" -> (right * left)
    |"/" -> (right / left)
    |"%" -> (right mod left)
    |"<"  -> boolnumeric (right < left)
    |"<=" -> boolnumeric (right <= left)
    |">"  -> boolnumeric (right > left)
    |">=" -> boolnumeric (right >= left)
    |"==" -> boolnumeric (right == left)
    |"!=" -> boolnumeric (right != left)
    |"!!" -> boolnumeric (numericbool right || numericbool left)
    |"&&" -> boolnumeric (numericbool right && numericbool left)
    | _ -> failwith "Error"

      let binarylist operatorslist = 
      let listof operators = (ostap ($(operators)), 
      fun expr1 expr2 -> Binop (operators, expr1, expr2)) in 
      List.map listof operatorslist;;  
    
    let rec eval env ((statement, input, output, r) as sior) expr = 
    match expr with
    | Var v -> let result = State.eval statement v in	(statement, input, output, Some result)
    | Const c -> (statement, input, output, Some (Value.of_int c))
    | Array e -> let (statement, input, output, rt) = eval_list env sior e in env#definition env "$array" rt (statement, input, output, None)
    | String s -> (statement, input, output, Some (Value.of_string s))
    | Binop (operators, expr1, expr2) ->
     let (_, _, _, Some l) as sior' = eval env sior expr1 in
     let (statemen', input', output', Some r) = eval env sior' expr2 in
     let numbers = (comp operators (Value.to_int l) (Value.to_int r)) in 
     (statement, input, output, Some (Value.of_int numbers))
    | Elem (a, indx) -> 
        let (_, _, _, Some value_a) as sior = eval env sior a in 
        let (_, _, _, Some value_indx) as sior = eval env sior indx in 
        env#definition env "$elem" [value_a; value_indx] (statement, input, output, None)
    | Length a -> 
        let (statement, input, output, Some value_a) = eval env sior a in 
        env#definition env "$length" [value_a] (statement, input, output, None)  
    | Call (name, param) ->
        let (sior', param') = List.fold_left 
      	          (fun (sior, cv) expr -> let (_, _, _, Some v) as sior' = eval env sior expr in (sior', cv @ [v])) (sior, [])
     	          param in
      	env#definition env name param' sior'   
      and eval_list env sior xs =
       let vs, (statement, input, output, _) =
         List.fold_left
           (fun (cv, sior) x ->
              let (_, _, _, Some v) as sior = eval env sior x in
              v::cv, sior
           )
           ([], sior)
           xs
       in
       (statement, input, output, List.rev vs)
         
    (* Expression parser. You can use the following terminals:
    
         IDENT   --- a non-empty identifier a-zA-Z[a-zA-Z0-9_]* as a string
         DECIMAL --- a decimal constant [0-9]+ as a string                                                                                                                  
    *)
    ostap (
      parse: 
        !(Ostap.Util.expr
          (fun v -> v)
          [|
            `Lefta, binarylist ["!!"];
            `Lefta, binarylist ["&&"];
            `Nona,  binarylist [">="; ">"; "<="; "<"; "=="; "!="];
            `Lefta, binarylist ["+"; "-"];
            `Lefta, binarylist ["*"; "/"; "%"]
          |]
          primary
         );
         primary: 
        e:expr action:(
        -"[" i:parse -"]" {`Elem i} 
        | -"." %"length" {`Len}
      ) * {List.fold_left (fun x -> function `Elem i -> Elem (x, i) | `Len -> Length x) e action};  
      expr:
        name : IDENT "(" args:!(Util.list0)[parse] ")" {Call (name, args)}
        | variable: IDENT {Var (variable)}
        | const: DECIMAL {Const (const)}
        | str:STRING {String (String.sub str 1 (String.length str - 2))}
        | ch:CHAR {Const (Char.code ch)}
        | -"[" elements:!(Util.list0)[parse] -"]" {Array elements}
        | -"(" parse -")"
     ) 
  end
                    
(* Simple statements: syntax and sematics *)
module Stmt =
  struct

    (* The type for statements *)
    type t =
    (* assignment                       *) | Assign of string * Expr.t list * Expr.t
    (* composition                      *) | Seq    of t * t 
    (* empty statement                  *) | Skip
    (* conditional                      *) | If     of Expr.t * t * t
    (* loop with a pre-condition        *) | While  of Expr.t * t
    (* loop with a post-condition       *) | Repeat of Expr.t * t
    (* return statement                 *) | Return of Expr.t option
    (* call a procedure                 *) | Call   of string * Expr.t list
                                                                    
    (* Statement evaluator
    
         val eval : env -> config -> t -> config
         
       Takes an environment, a configuration and a statement, and returns another configuration. The 
       environment is the same as for expressions
    *)

    let update st x v is =
      let rec update a v = function
      | []    -> v           
      | i::tl ->
          let i = Value.to_int i in
          (match a with
           | Value.String s when tl = [] -> Value.String (Value.update_string s i (Char.chr @@ Value.to_int v))
           | Value.Array a               -> Value.Array  (Value.update_array  a i (update (List.nth a i) v tl))
          ) 
      in
      State.update x (match is with [] -> v | _ -> update (State.eval st x) v is) st
          
    let rec eval env sior k stmt =
    	let sk stmt k =
    		if k = Skip then stmt
    		else Seq (stmt, k) in
      match stmt, sior with
    	| Assign (x, indexes, e), (statement, input, output, r) -> 
    	let (statement', input', output', indx) = Expr.eval_list env sior indexes in
    	let (statement', input', output', Some value) = Expr.eval env (statement', input', output', None) e in
        eval env (update statement' x value indx, input', output', None) Skip k
    	| Seq (a, b), sior ->
        eval env sior (sk b k) a        
    	| Skip, sior -> 
    		if k = Skip then sior
        else eval env sior Skip k       
    	| If (cond, the, els), (statement, input, output, r) ->
    		let (statement', input', output', Some value) as sior' = Expr.eval env sior cond in
    		if Value.to_int value == 0 then eval env sior' k els  
    		else eval env sior' k the      
    	| While (cond, body), sior ->
    	let (statement', input', output', Some res_cond) as sior' = Expr.eval env sior cond in
        if Value.to_int res_cond == 0 then eval env sior' Skip k
        else eval env sior' (sk stmt k) body      
    	| Repeat (cond, body), sior ->
        eval env sior (sk ( While(Expr.Binop("==", cond, Expr.Const 0), body)) k) body        
    	| Call (func, args), sior ->
        let sior' = Expr.eval env sior (Expr.Call (func, args)) in
        eval env sior' Skip k   
      | Return expr, (statement, input, output, r) -> 
      (
        match expr with
        | None -> (statement, input, output, None)
        | Some expr -> Expr.eval env sior expr
      )

    let rec parse_elif_acts elif_acts parsed_else_act = 
      match elif_acts with
      [] -> parsed_else_act
      | (cond, act)::tail -> If (cond, act, parse_elif_acts tail parsed_else_act)

    let parse_elif_else elif_acts else_act = 
      let parsed_else_act = 
        match else_act with
        | None -> Skip
        | Some act -> act
      in parse_elif_acts elif_acts parsed_else_act
         
    (* Statement parser *)
    ostap (
      parse: 
        left_stmt:stmt -";" right_stmt:parse {Seq (left_stmt, right_stmt)} | stmt;
      stmt: 
        variable:IDENT indx:(-"[" !(Expr.parse) -"]") * -":=" expr:!(Expr.parse) {Assign (variable, indx, expr)}
        | %"skip" {Skip}
        | %"while" expr:!(Expr.parse) %"do" body:parse %"od" {While (expr, body)}
        | %"repeat" body:parse %"until" expr:!(Expr.parse) {Repeat (expr, body)}
        | %"for" init:parse -"," expr:!(Expr.parse) -"," loopexpr:parse %"do" body:parse %"od" {Seq (init, While (expr, Seq (body, loopexpr)))}
        | %"if" expr:!(Expr.parse) %"then" at:parse aels:else_body %"fi" {If (expr, at, aels)}
        | name : IDENT "(" args:!(Util.list0)[Expr.parse] ")" {Call (name, args)}
        | %"return" expr:!(Expr.parse)? {Return (expr)}; 
      else_body:
        %"else" aels:parse {aels}
        | %"elif" expr:!(Expr.parse) %"then" at:parse aels:else_body {If (expr, at, aels)}
        | "" {Skip}
    )
      
  end

(* Function and procedure definitions *)
module Definition =
  struct

    (* The type for a definition: name, argument list, local variables, body *)
    type t = string * (string list * string list * Stmt.t)

    ostap (
      arg  : IDENT;
      parse: %"fun" name:IDENT "(" args:!(Util.list0 arg) ")"
         locs:(%"local" !(Util.list arg))?
        "{" body:!(Stmt.parse) "}" {
        (name, (args, (match locs with None -> [] | Some l -> l), body))
      }
    )

  end
    
(* The top-level definitions *)

(* The top-level syntax category is a pair of definition list and statement (program body) *)
type t = Definition.t list * Stmt.t    

(* Top-level evaluator

     eval : t -> int list -> int list
     
   Takes a program and its input stream, and returns the output stream
*)
let eval (defs, body) i =
  let module M = Map.Make (String) in
  let m          = List.fold_left (fun m ((name, _) as def) -> M.add name def m) M.empty defs in  
  let _, _, o, _ =
    Stmt.eval
      (object
         method definition env f args ((st, i, o, r) as conf) =
           try
             let xs, locs, s      =  snd @@ M.find f m in
             let st'              = List.fold_left (fun st (x, a) -> State.update x a st) (State.enter st (xs @ locs)) (List.combine xs args) in
             let st'', i', o', r' = Stmt.eval env (st', i, o, r) Stmt.Skip s in
             (State.leave st'' st, i', o', r')
           with Not_found -> Builtin.eval conf args f
       end)
      (State.empty, i, [], None)
      Stmt.Skip
      body
  in
  o

(* Top-level parser *)
let parse = ostap (!(Definition.parse)* !(Stmt.parse))
