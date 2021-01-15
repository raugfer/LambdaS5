open Lexing
open Prelude

type oattr = 
  | Proto
  | Klass
  | Extensible
  | Primval
  | Code

let string_of_oattr oattr = match oattr with
  | Proto -> "#proto"
  | Klass -> "#class"
  | Extensible -> "#extensible"
  | Primval -> "#primval"
  | Code -> "#code"

type pattr =
  | Value
  | Getter
  | Setter
  | Config
  | Writable
  | Enum

let string_of_attr attr = match attr with
  | Value -> "#value"
  | Getter -> "#getter"
  | Setter -> "#setter"
  | Config -> "#configurable"
  | Writable -> "#writable"
  | Enum -> "#enumerable"

type exp =
  | Null of Pos.t
  | Undefined of Pos.t
  | String of Pos.t * string
  | Num of Pos.t * float
  | True of Pos.t
  | False of Pos.t
  | Id of Pos.t * id
  | Object of Pos.t * attrs * (string * prop) list
      (* GetAttr (Pos.t, property, object, field name) *)
  | GetAttr of Pos.t * pattr * exp * exp
      (* SetAttr (Pos.t, property, object, field name, new value) *)
  | SetAttr of Pos.t * pattr * exp * exp * exp
  | GetObjAttr of Pos.t * oattr * exp
  | SetObjAttr of Pos.t * oattr * exp * exp
  | GetField of Pos.t * exp * exp * exp (*Pos.t, left, right, args object *)
  | SetField of Pos.t * exp * exp * exp * exp (* Pos.t, obj, field, new val, args *)
  | DeleteField of Pos.t * exp * exp (* Pos.t, obj, field *)
  | OwnFieldNames of Pos.t * exp
  | SetBang of Pos.t * id * exp
  | Op1 of Pos.t * string * exp
  | Op2 of Pos.t * string * exp * exp
  | If of Pos.t * exp * exp * exp
  | App of Pos.t * exp * exp list
  | Seq of Pos.t * exp * exp
  | Let of Pos.t * id * exp * exp
  | Rec of Pos.t * id * exp * exp (** value bound must be an [ELambda] *)
  | Label of Pos.t * id * exp
  | Break of Pos.t * id * exp
  | TryCatch of Pos.t * exp * exp
      (** Catch block must be an [ELambda] *)
  | TryFinally of Pos.t * exp * exp
  | Throw of Pos.t * exp
  | Lambda of Pos.t * id list * exp
  | Eval of Pos.t * exp * exp (* Pos.t, string to be evaled, env object  *)
  | Hint of Pos.t * string * exp
and data =       
    {value : exp;
     writable : bool; }
and accessor =       
    {getter : exp;
     setter : exp; }
and prop =
  | Data of data * bool * bool
  | Accessor of accessor * bool * bool
and attrs =
    { primval : exp option;
      code : exp option;
      proto : exp option;
      klass : string;
      extensible : bool; }

(* Some useful defaults for these things, to avoid typing too much *)
let d_attrs = 
  { primval = None;
    code = None;
    proto = Some (Null Pos.dummy);
    klass = "Object";
    extensible = true; }

let d_data =
  { value = Undefined Pos.dummy;
    writable = true; }

let d_accessor = 
  { getter = Undefined Pos.dummy;
    setter = Undefined Pos.dummy; }

let pos_of exp = match exp with
  | Null pos -> pos
  | Undefined pos -> pos
  | String (pos, _) -> pos
  | Num (pos, _) -> pos
  | True pos -> pos
  | False pos -> pos
  | Id (pos, _) -> pos
  | Object (pos, _, _) -> pos
  | GetAttr (pos, _, _, _) -> pos
  | SetAttr (pos, _, _, _, _) -> pos
  | GetObjAttr (pos, _, _) -> pos
  | SetObjAttr (pos, _, _, _) -> pos
  | GetField (pos, _, _, _) -> pos 
  | SetField (pos, _, _, _, _) -> pos 
  | DeleteField (pos, _, _) -> pos
  | OwnFieldNames (pos, _) -> pos
  | SetBang (pos, _, _) -> pos
  | Op1 (pos, _, _) -> pos
  | Op2 (pos, _, _, _) -> pos
  | If (pos, _, _, _) -> pos
  | App (pos, _, _) -> pos
  | Seq (pos, _, _) -> pos
  | Let (pos, _, _, _) -> pos
  | Rec (pos, _, _, _) -> pos
  | Label (pos, _, _) -> pos
  | Break (pos, _, _) -> pos
  | TryCatch (pos, _, _) -> pos
  | TryFinally (pos, _, _) -> pos
  | Throw (pos, _) -> pos
  | Lambda (pos, _, _) -> pos
  | Eval (pos, _, _) -> pos
  | Hint (pos, _, _) -> pos

let child_exps (exp : exp) : exp list =
  let data_child_exps {value = x; writable = _} = [x] in
  let accessor_child_exps {getter = x; setter = y} = [x; y] in
  let prop_child_exps prop = match prop with
    | Data (data, _, _) -> data_child_exps data
    | Accessor (accessor, _, _) -> accessor_child_exps accessor in
  let prop_list_child_exps proplist =
    List.concat (map (fun (_, prop) -> prop_child_exps prop) proplist) in
  let option_to_list option = match option with
    | None -> []
    | Some x -> [x] in
  let attrs_child_exps attrs = match attrs with
      {primval = exp1; code = exp2; proto = exp3; klass = _; extensible = _} ->
        List.concat (map option_to_list [exp1; exp2; exp3]) in
  match exp with
  | Null _ -> []
  | Undefined _ -> []
  | String _ -> []
  | Num _ -> []
  | True _ -> []
  | False _ -> []
  | Id _ -> []
  | Object (_, attrs, props) ->
    attrs_child_exps attrs @ prop_list_child_exps props
  | GetAttr (_, _, x, y) -> [x; y]
  | SetAttr (_, _, x, y, z) -> [x; y; z]
  | GetObjAttr (_, _, x) -> [x]
  | SetObjAttr (_, _, x, y) -> [x; y]
  | GetField (_, x, y, z) -> [x; y; z]
  | SetField (_, x, y, z, w) -> [x; y; z; w]
  | DeleteField (_, x, y) -> [x; y]
  | OwnFieldNames (_, x) -> [x]
  | SetBang (_, _, x) -> [x]
  | Op1 (_, _, x) -> [x]
  | Op2 (_, _, x, y) -> [x; y]
  | If (_, x, y, z) -> [x; y; z]
  | App (_, x, ys) -> x :: ys
  | Seq (_, x, y) -> [x; y]
  | Let (_, _, x, y) -> [x; y]
  | Rec (_, _, x, y) -> [x; y]
  | Label (_, _, x) -> [x]
  | Break (_, _, x) -> [x]
  | TryCatch (_, x, y) -> [x; y]
  | TryFinally (_, x, y) -> [x; y]
  | Throw (_, x) -> [x]
  | Lambda (_, _, x) -> [x]
  | Eval (_, x, y) -> [x; y]
  | Hint (_, _, x) -> [x]

let rec free_vars (exp : exp) : IdSet.t =
  match exp with
  | Id (_, var) ->
    IdSet.singleton var
  | SetBang (_, var, exp) ->
    IdSet.add var (free_vars exp)
  | Let (_, var, defn, body) ->
    IdSet.union (free_vars defn) (IdSet.remove var (free_vars body))
  | Rec (_, var, defn, body) ->
    IdSet.remove var (IdSet.union (free_vars defn) (free_vars body))
  | Lambda (_, vars, body) ->
    List.fold_left (flip IdSet.remove) (free_vars body) vars
  | Eval (_, str_exp, env_exp) ->
    IdSet.union (free_vars str_exp) (free_vars env_exp)
  | exp ->
    List.fold_left IdSet.union IdSet.empty (map free_vars (child_exps exp))

let rec gen_js_exp exp =
  let c =
    match exp with
    | Null (p) -> "{ type: 'Null', pos: " ^ (gen_js_pos p) ^ " }"
    | Undefined (p) -> "{ type: 'Undefined', pos: " ^ (gen_js_pos p) ^ " }"
    | String (p, v) -> "{ type: 'String', pos: " ^ (gen_js_pos p) ^ ", value: " ^ (gen_js_str v) ^ " }"
    | Num (p, v) -> "{ type: 'Num', pos: " ^ (gen_js_pos p) ^ ", value: " ^ (gen_js_num v) ^ " }"
    | True (p) -> "{ type: 'Bool', pos: " ^ (gen_js_pos p) ^ ", value: true }"
    | False (p) -> "{ type: 'Bool', pos: " ^ (gen_js_pos p) ^ ", value: false }"
    | Id (p, v) -> "{ type: 'Id', pos: " ^ (gen_js_pos p) ^ ", id: " ^ (gen_js_str v) ^ " }"
    | Object (p, a, ps) -> "{ type: 'Object', pos: " ^ (gen_js_pos p) ^ ", attrs: " ^ (gen_js_attrs a) ^ ", props: [" ^ (gen_js_props ps) ^ "] }"
    | GetAttr (p, a, x, y) -> "{ type: 'GetAttr', pos: " ^ (gen_js_pos p) ^ ", attr: " ^ (gen_js_pattr a) ^ ", obj: " ^ (gen_js_exp x) ^ ", field: " ^ (gen_js_exp y) ^ " }"
    | SetAttr (p, a, x, y, z) -> "{ type: 'SetAttr', pos: " ^ (gen_js_pos p) ^ ", attr: " ^ (gen_js_pattr a) ^ ", obj: " ^ (gen_js_exp x) ^ ", field: " ^ (gen_js_exp y) ^ ", value: " ^ (gen_js_exp z) ^ " }"
    | GetObjAttr (p, a, x) -> "{ type: 'GetObjAttr', pos: " ^ (gen_js_pos p) ^ ", attr: " ^ (gen_js_oattr a) ^ ", obj: " ^ (gen_js_exp x) ^ " }"
    | SetObjAttr (p, a, x, y) -> "{ type: 'SetObjAttr', pos: " ^ (gen_js_pos p) ^ ", attr: " ^ (gen_js_oattr a) ^ ", obj: " ^ (gen_js_exp x) ^ ", values: " ^ (gen_js_exp y) ^ " }"
    | GetField (p, x, y, z) -> "{ type: 'GetField', pos: " ^ (gen_js_pos p) ^ ", obj: " ^ (gen_js_exp x) ^ ", field: " ^ (gen_js_exp y) ^ ", arg: " ^ (gen_js_exp z) ^ " }"
    | SetField (p, x, y, z, w) -> "{ type: 'SetField', pos: " ^ (gen_js_pos p) ^ ", obj: " ^ (gen_js_exp x) ^ ", field: " ^ (gen_js_exp y) ^ ", value: " ^ (gen_js_exp z) ^ ", args: " ^ (gen_js_exp w) ^ " }"
    | DeleteField (p, x, y) -> "{ type: 'DeleteField', pos: " ^ (gen_js_pos p) ^ ", obj: " ^ (gen_js_exp x) ^ ", field: " ^ (gen_js_exp y) ^ " }"
    | OwnFieldNames (p, x) -> "{ type: 'OwnFieldNames', pos: " ^ (gen_js_pos p) ^ ", obj: " ^ (gen_js_exp x) ^ " }"
    | SetBang (p, x, y) -> "{ type: 'SetBang', pos: " ^ (gen_js_pos p) ^ ", id: " ^ (gen_js_str x) ^ ", exp: " ^ (gen_js_exp y) ^ " }"
    | Op1 (p, x, y) -> "{ type: 'Op1', pos: " ^ (gen_js_pos p) ^ ", op: " ^ (gen_js_str x) ^ ", arg: " ^ (gen_js_exp y) ^ " }"
    | Op2 (p, x, y, z) -> "{ type: 'Op2', pos: " ^ (gen_js_pos p) ^ ", op: " ^ (gen_js_str x) ^ ", arg1: " ^ (gen_js_exp y) ^ ", arg2: " ^ (gen_js_exp z) ^ " }"
    | If (p, x, y, z) -> "{ type: 'If', pos: " ^ (gen_js_pos p) ^ ", cond: " ^ (gen_js_exp x) ^ ", exp1: " ^ (gen_js_exp y) ^ ", exp2: " ^ (gen_js_exp z) ^ " }"
    | App (p, x, ys) -> "{ type: 'App', pos: " ^ (gen_js_pos p) ^ ", func: " ^ (gen_js_exp x) ^ ", args: [" ^ (gen_js_exps ys) ^ "] }"
    | Seq (p, x, y) -> "{ type: 'Seq', pos: " ^ (gen_js_pos p) ^ ", exp1: " ^ (gen_js_exp x) ^ ", exp2: " ^ (gen_js_exp y) ^ " }"
    | Let (p, x, y, z) -> "{ type: 'Let', pos: " ^ (gen_js_pos p) ^ ", id: " ^ (gen_js_str x) ^ ", defn: " ^ (gen_js_exp y) ^ ", body: " ^ (gen_js_exp z) ^ " }"
    | Rec (p, x, y, z) -> "{ type: 'Rec', pos: " ^ (gen_js_pos p) ^ ", id: " ^ (gen_js_str x) ^ ", defn: " ^ (gen_js_exp y) ^ ", body: " ^ (gen_js_exp z) ^ " }"
    | Label (p, x, y) -> "{ type: 'Label', pos: " ^ (gen_js_pos p) ^ ", id: " ^ (gen_js_str x) ^ ", exp: " ^ (gen_js_exp y) ^ " }"
    | Break (p, x, y) -> "{ type: 'Break', pos: " ^ (gen_js_pos p) ^ ", id: " ^ (gen_js_str x) ^ ", exp: " ^ (gen_js_exp y) ^ " }"
    | TryCatch (p, x, y) -> "{ type: 'TryCatch', pos: " ^ (gen_js_pos p) ^ ", body: " ^ (gen_js_exp x) ^ ", cat: " ^ (gen_js_exp y) ^ " }"
    | TryFinally (p, x, y) -> "{ type: 'TryFinally', pos: " ^ (gen_js_pos p) ^ ", body: " ^ (gen_js_exp x) ^ ", fin: " ^ (gen_js_exp y) ^ " }"
    | Throw (p, x) -> "{ type: 'Throw', pos: " ^ (gen_js_pos p) ^ ", exp: " ^ (gen_js_exp x) ^ " }"
    | Lambda (p, x, y) -> "{ type: 'Lambda', pos: " ^ (gen_js_pos p) ^ ", ids: [" ^ (gen_js_strs x) ^ "], body: " ^ (gen_js_exp y) ^ " }"
    | Eval (p, x, y) -> "{ type: 'Eval', pos: " ^ (gen_js_pos p) ^ ", e: " ^ (gen_js_exp x) ^ ", bindings: " ^ (gen_js_exp y) ^ " }"
    | Hint (p, x, y) -> "{ type: 'Hint', pos: " ^ (gen_js_pos p) ^ ", s: " ^ (gen_js_str x) ^ ", e: " ^ (gen_js_exp y) ^ " }"
  in
    c ^ "\n"

and gen_js_attrs attrs =
  let primval = match attrs.primval with None -> "null" | Some (e) -> gen_js_exp e in
  let code = match attrs.code with None -> "null" | Some (e) -> gen_js_exp e in
  let proto = match attrs.proto with None -> "null" | Some (e) -> gen_js_exp e in
  let klass = gen_js_str attrs.klass in
  let extensible = gen_js_bool attrs.extensible in
  "{ primval: " ^ primval ^ ", code: " ^ code ^ ", proto: " ^ proto ^ ", klass: " ^ klass ^ ", extensible: " ^ extensible ^ " }"

and gen_js_prop (s, prop) =
  let meta =
    match prop with
    | Data ({ value = v; writable = write; }, enum, config) ->
      let value = gen_js_exp v in
      let writable = gen_js_bool write in
      let enumerable = gen_js_bool enum in
      let configurable = gen_js_bool config in
      "{ type: 'Data', data: { value: " ^ value ^ ", writable: " ^ writable ^ " }, enumerable: " ^ enumerable ^ ", configurable: " ^ configurable ^ " }"
    | Accessor ({ getter = get; setter = set; }, enum, config) ->
      let getter = gen_js_exp get in
      let setter = gen_js_exp set in
      let enumerable = gen_js_bool enum in
      let configurable = gen_js_bool config in
      "{ type: 'Accessor', accessor: { getter: " ^ getter ^ ", setter: " ^ setter ^ " }, enumerable: " ^ enumerable ^ ", configurable: " ^ configurable ^ " }"
  in
  "[" ^ (gen_js_str s) ^ ", " ^ meta ^ "]"

and gen_js_oattr attr = 
  match attr with
  | Proto -> "'Proto'"
  | Klass -> "'Klass'"
  | Extensible -> "'Extensible'"
  | Primval -> "'Primval'"
  | Code -> "'Code'"

and gen_js_pattr attr =
  match attr with
  | Value -> "'Value'"
  | Getter -> "'Getter'"
  | Setter -> "'Setter'"
  | Config -> "'Config'"
  | Writable -> "'Writable'"
  | Enum -> "'Enum'"

and gen_js_bool b = if b then "true" else "false"

and gen_js_num n =
  let v = string_of_float n in
    if v = "nan" then "NaN" else
    if v = "inf" then "Infinity" else
    if v = "-inf" then "-Infinity" else
    v

and gen_js_int n = string_of_int n

and gen_js_str s = "'" ^ (Str.global_replace (Str.regexp_string "'") "\\'" s) ^ "'"

and gen_js_strs ss =
  match ss with
  | [] -> ""
  | [first] -> gen_js_str first
  | first :: rest -> (gen_js_str first) ^ ", " ^ (gen_js_strs rest)

and gen_js_exps exps =
  match exps with
  | [] -> ""
  | [first] -> gen_js_exp first
  | first :: rest -> (gen_js_exp first) ^ ", " ^ (gen_js_exps rest)

and gen_js_props ps =
  match ps with
  | [] -> ""
  | [first] -> gen_js_prop first
  | first :: rest -> (gen_js_prop first) ^ ", " ^ (gen_js_props rest)

and gen_js_pos p =
  if Pos.compare p Pos.dummy = 0
  then "[null, null, true]"
  else begin
    let (s, e, b) = p in
    let start = "{ pos_fname: " ^ (gen_js_str s.pos_fname) ^ ", pos_lnum: " ^ (gen_js_int s.pos_lnum) ^ ", pos_bol: " ^ (gen_js_int s.pos_bol) ^ ", pos_cnum: " ^ (gen_js_int s.pos_cnum) ^ " }" in
    let _end = "{ pos_fname: " ^ (gen_js_str e.pos_fname) ^ ", pos_lnum: " ^ (gen_js_int e.pos_lnum) ^ ", pos_bol: " ^ (gen_js_int e.pos_bol) ^ ", pos_cnum: " ^ (gen_js_int e.pos_cnum) ^ " }" in
    "[" ^ start ^ ", " ^ _end ^ ", " ^ (gen_js_bool b) ^ "]"
  end
