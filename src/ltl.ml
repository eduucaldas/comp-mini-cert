open Ltltree

let graph = ref Label.M.empty

let lookup colored r =
  if Register.is_hw r then
    Reg r
  else
    Register.M.find r colored

let instr colored frame_size = function
  | Ertltree.Eload (r1, n, r2, l) ->
      Ltltree.Eload (r1, n, r2, l)
  | Ertltree.Estore (r1, r2, n, l) ->
      Ltltree.Estore (r1, r2, n, l)
  | Ertltree.Egoto (l) ->
      Ltltree.Egoto (l)
  | Ertltree.Ereturn ->
      Ltltree.Ereturn
  | Ertltree.Econst (n, r, l) ->
      Econst (n, lookup colored r, l)
  | _ -> assert false

let ertl_to_ltl colored (l:Label.t) (i:Ertltree.instr) =
  let instr_ltl = instr i in
  graph := Label.M.add l instr_ltl !graph

let deffun (df: Ertltree.deffun) = 
  graph := Label.M.empty;
  let live_analysis = Life.liveness df.fun_body in
  let ig = Interference.make live_analysis in
  let colored = Interference.color ig in
  Label.M.iter (ertl_to_ltl colored) df.fun_body;
  {
    fun_name = df.fun_name;
    fun_entry = df.fun_entry;
    fun_body = !graph;
  }

let program (file: Ertltree.file) =
  { funs = List.map deffun file.funs}