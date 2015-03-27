open Prelude
open Ljs_syntax
open Ljs_opt
module EU = Exp_util

(* TODO: should the opt phase check type error? e.g.
   to check the op1 args has the right type for op1.
 *)

(* try to simplify the op1, 
 * return new exp in option on success, None otherwise.
 * Note: the e should be a simplified exp.
 *)
let fold_const_op1 (p : Pos.t) (op : string) (e : exp) : exp option =
  EU.apply_op1 p op e

let fold_const_op2 (p : Pos.t) (op : string) (e1 : exp) (e2 : exp) : exp option = 
  EU.apply_op2 p op e1 e2

let rec fold_const_app pos lambda args =
  Null pos
  
let rec fold_const (e : exp) : exp =
  match e with
  | Undefined _ 
  | Null _ 
  | String (_, _)
  | Num (_, _)
  | True _ 
  | False _ 
  | Id (_, _) -> e
  | Op1 (p, op, e) ->
     let newe = fold_const e in
     begin match fold_const_op1 p op newe with
       | Some (folded) -> folded
       | None -> Op1 (p, op, newe)
     end
  | Op2 (p, op, e1, e2) ->
     let newe1 = fold_const e1 in
     let newe2 = fold_const e2 in
     begin match fold_const_op2 p op newe1 newe2 with
       | Some (folded) -> folded
       | None -> Op2 (p, op, newe1, newe2)
     end
  | If (p, cond, thn, els) ->
     let c_val = fold_const cond in
     begin
       match c_val with
       | True _ -> fold_const thn
       | False _ 
       | Null _
       | Undefined _
       | Num (_,_)
       | String (_,_)
       | Lambda (_,_,_)
       | Object (_,_,_) -> fold_const els 
       | _ -> 
          begin
            let t = fold_const thn in
            let e = fold_const els in
            If (p, c_val, t, e)
          end 
     end 
  | GetAttr (_, _, _, _)
  | GetObjAttr (_, _, _)
  | GetField (_, _, _, _)
  | Object (_,_,_) 
  | SetAttr (_,_,_,_,_)
  | SetObjAttr (_,_,_,_)
  | SetField (_,_,_,_,_)
  | DeleteField (_, _, _) 
  | OwnFieldNames (_,_)
  | SetBang (_,_,_)
  | Lambda (_,_,_)
  | Seq (_,_,_) 
  | Let (_,_,_,_)
  | Rec (_,_,_,_)
  | App (_, _, _)
  | Label (_, _, _)
  | TryCatch (_, _, _)
  | Break (_,_,_)
  | TryFinally (_,_,_)
  | Throw (_,_)
  | Hint (_,_,_)
    -> optimize fold_const e

