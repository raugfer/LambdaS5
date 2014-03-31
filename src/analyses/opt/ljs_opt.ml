open Ljs_syntax

type node = {
  block: exp;
  edgeIn: (node list) ref;
  edgeOut: (node list) ref;
}

(* cfg is used to describe a control flow graph. A cfg
consists of a `first` node, which is the node that flow 
comes into, and a set of `last` nodes, which the flow goes
out from *)
type cfg = {
  first: node;
  last : node list;
}

(* add edges from node1 to node2. node1's out edge will
   include node2 and node2's in edge will include node1 *)
(* val add_edge : node->node *)
let add_edge node1 node2 =
  node1.edgeOut :=  node2 :: (! node1.edgeOut) ;
  node2.edgeIn  :=  node1 :: (! node2.edgeIn)
;;

(* add list of nodes as the in-nodes of the second argument *)
(* val add_edges: node list -> node -> None *)
let add_edges n_list node2 =
  let add_single n1 =
    add_edge n1 node2 in
  List.map add_single n_list
;;

(* map from string(ret id in this case) to something else *)
module StringMap = Map.Make(String);;

(* cfg StringMap -> exp -> cfg *)
let build_graph labelMap e =
  let meta_node exp =
    { block = exp; edgeIn = ref 0; edgeOut = ref 0 } in
  let meta_cfg node =
    { first = node; last = [node] } in
  match e with
  | Seq (_, e1, e2) ->
     let g1 = build_graph labelMap e1 in
     let g2 = build_graph labelMap e2 in
     add_edges g1.last g2.first;
     {first = g1.first ; last = g2.last}

  | If (_, tst, thn, els) ->
     let g1 = build_graph labelMap tst in
     let g2 = build_graph labelMap thn in
     let g3 = build_graph labelMap els in
     add_edges g1.last g2.first;
     add_edges g1.last g3.first;
     {first = g1.first ; last = List.append g2.last g3.last}

  | App (_, f, args) ->
     let g1 = build_graph labelMap f in
     let g_list = List.map (fun(arg : exp) -> build_graph labelMap arg)
                           args
     in 
     let walk_args (prev:cfg)(nexts:cfg list) =
       match nexts with
       | l :: [] -> 
          add_edges prev.last l.first; 
          l
       | f :: l  -> 
          add_edges prev.last f.first;
          walk_args f l
     in
     let last_cfg = walk_args g1 g_list in 
     { first = g1.first ; last = last_cfg.last }

  | Let (_, id, e, body) ->
     let g1 = build_graph labelMap e in
     let g2 = build_graph labelMap body in
     add_edges g1.last g2.first;
     { first = g1.first ; last = g2.last }

  | Rec (_, id, e, body) ->
     let g1 = build_graph labelMap e in
     let g2 = build_graph labelMap body in
     add_edges g1.last g2.first;
     { first = g1.first ; last = g2.last }

  | Label (pos, id, body) -> (* the id is a string *)
     let g1 = build_graph labelMap Id(pos, id) in
     let new_labelMap = Map.add id g1 in
     let g2 = build_graph new_labelMap body in
     (* flow from body to ret *)
     add_edges g2.last g1.first;
     { first = g2.first ; last = g1.last }

  | Break (pos, id, body) ->
     let g1 = build_graph labelMap Id(pos, id) in
     let g2 = build_graph labelMap body in
     let return_node = StringMap.find id labelMap in
     (* body -> ret id *)
     add_edges g2.last g1.first; 
     (* ret id -> cfg *)
     add_edges g1.last return_node.first;
     (* comes into body, goes out from ret id *)
     { first = g2.first; last = g1.last }

  (* TODO: add tryCatch and tryFinally *)

  | _ -> meta_cfg (meta_node e)

(* use the map:
let m = StringMap.empty;;
let m = StringMap.add id node m;;
let m = StringMap.add id1 node1 m;;
 *)
