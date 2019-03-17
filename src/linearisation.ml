open X86_64

type instr = Code of text | Label of Label.t

let (visited:(Label.t, unit) Hashtbl.t) = Hashtbl.create 17

let code = ref []

let labels = Hashtbl.create 17

let emit l i = code := Code i :: Label l :: !code

let emit_wl i = code := Code i :: !code

let need_label l = Hashtbl.add labels l ()

let operand = function
  | Ltltree.Reg r -> reg (register64 r)
  | Ltltree.Spilled fs -> ind ~ofs:fs rbp

let operandB = function
  | Ltltree.Reg r -> reg (register8 (register64 r))
  | Ltltree.Spilled fs -> reg (register8 (register64 Register.tmp1))

let barith_to_64 op r1 r2 =
  let rq1 = operand r1 in
  match op with
  | Ops.Mmov ->  movq rq1 (operand r2)
  | Ops.Madd ->  addq rq1 (operand r2)
  | Ops.Msub ->  subq rq1 (operand r2)
  | Ops.Mmul -> imulq rq1 (operand r2)
  | Ops.Mdiv -> emit_wl cqto; idivq rq1
  | _ -> assert false

let emit_binop_to_64 (op:Ops.mbinop) (r1:Ltltree.operand) (r2:Ltltree.operand) l =
  match op with
  | Ops.Mmov | Ops.Madd | Ops.Msub | Ops.Mmul | Ops.Mdiv -> emit l (barith_to_64 op r1 r2)
  | Ops.Msete | Ops.Msetne | Ops.Msetl | Ops.Msetle | Ops.Msetg | Ops.Msetge -> (
      emit_wl (cmpq (operand r1) (operand r2));
      emit_wl (movq (imm32 Int32.zero) (operand r2));
      let rb2 = operandB r2 in
      (match op with
       | Ops.Msete  -> emit l (sete  rb2)
       | Ops.Msetne -> emit l (setne rb2)
       | Ops.Msetl  -> emit l (setl  rb2)
       | Ops.Msetle -> emit l (setle rb2)
       | Ops.Msetg  -> emit l (setg  rb2)
       | Ops.Msetge -> emit l (setge rb2)
       | _ -> assert false
      );
      (match r2 with
       | Ltltree.Spilled fs -> emit_wl (movb rb2 (ind ~ofs:fs rbp))
       | _ -> ()
      )
    )


let unop_to_64 (op:Ops.munop) (r:Ltltree.operand) =
  let rq = operand r in
  match op with
  | Ops.Maddi i ->
    addq (imm32 i) rq
  | Ops.Msetei i ->
    emit_wl (cmpq (imm32 i) rq);
    sete (operandB r)
  | Ops.Msetnei i ->
    emit_wl (cmpq (imm32 i) rq);
    setne (operandB r)

let ubranch_to_64 br r =
  let n, brx = (
    match br with
    | Ops.Mjz -> Int32.zero, jz
    | Ops.Mjnz -> Int32.zero, jnz
    | Ops.Mjlei i -> i, jle
    | Ops.Mjgi i -> i, jg
  ) in
  emit_wl (cmpq (imm32 n) (operand r));
  brx

let bbranch_to_64 br r1 r2 =
  emit_wl (cmpq (operand r1) (operand r2));
  match br with
  | Ops.Mjl -> jl
  | Ops.Mjle -> jle

let rec lin (g:Ltltree.cfg) l =
  if not (Hashtbl.mem visited l) then (
    Hashtbl.add visited l ();
    instr g l (Label.M.find l g)
  )
  else (
    need_label l;
    emit_wl (jmp (l :> string))
  )

(*dont forget optimisation *)
and lin_brx (g:Ltltree.cfg) brx lt lf l =
  let lt_seen, lf_seen = Hashtbl.mem visited lt, Hashtbl.mem visited lf in
  if not lf_seen || not lt_seen then (
    emit l (brx (lt :> label));
    lin g lf;
    lin g lt;
    need_label lt
  ) else (
    need_label lt;
    need_label lf;
    emit l (brx (lt :> label));
    emit_wl (jmp (lf :> label))
  )

and instr g l = function
  | Ltltree.Econst (n, r, l1) ->
    emit l (movq (imm32 n) (operand r)); lin g l1
  | Ltltree.Ereturn ->
    emit l ret
  | Ltltree.Emunop (op, r, l1) ->
    emit l (unop_to_64 op r);
    lin g l1
  | Ltltree.Embinop (op, r1, r2, l1) ->
    emit_binop_to_64 op r1 r2 l;
    lin g l1
  | Ltltree.Eload (r_p1, n, r_p2, l1) ->
    emit l (movq (ind ~ofs:n (register64 r_p1)) (reg (register64 r_p2)));
    lin g l1
  | Ltltree.Estore (r_p1, r_p2, n, l1) ->
    emit l (movq (reg (register64 r_p1)) (ind ~ofs:n (register64 r_p2)) );
    lin g l1
  | Ltltree.Egoto (l1) ->
    if Hashtbl.mem visited l1 then (
      emit l (jmp (l1 :> label));
      need_label l1
    ) else
      code := Label l :: !code; (*ugly*)
    lin g l1
  | Ltltree.Epop (r_p, l1) ->
    emit l (popq (register64 r_p)); lin g l1
  | Ltltree.Epush (r, l1) ->
    emit l (pushq (operand r)); lin g l1
  | Ltltree.Emubranch (br, r, lt, lf) ->
    let brx = ubranch_to_64 br r in
    lin_brx g brx lt lf l
  | Ltltree.Embbranch (br, r1, r2, lt, lf) ->
    let brx = bbranch_to_64 br r1 r2 in
    lin_brx g brx lt lf l
  | Ltltree.Ecall (id, l1) ->
    emit l (call id);
    lin g l1

let deffun text (df: Ltltree.deffun) =
  code := [];
  text := !text ++ (label (df.fun_name :> label));
  lin df.fun_body df.fun_entry;
  let instr_to_text = function
    | Code c ->
      text := !text ++ c
    | Label l ->
      if Hashtbl.mem labels l then
        text := !text ++ (label (l :> label));
  in
  List.iter instr_to_text (List.rev !code);
  if (String.equal df.fun_name "main") then
    text := (globl df.fun_name) ++ !text

let program (file: Ltltree.file) =
  let file_text = ref nop in
  let file_data = ref nop in
  List.iter (deffun file_text) file.funs;
  {
    text = !file_text;
    data = !file_data
  }
