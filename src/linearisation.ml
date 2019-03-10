open X86_64

type instr = Code of text | Label of Label.t

let (visited:(Label.t, unit) Hashtbl.t) = Hashtbl.create 17

let code = ref []

let labels = Hashtbl.create 17

let emit l i = code := Code i :: Label l :: !code

let emit_wl i = code := Code i :: !code

let need_label l = Hashtbl.add labels l ()

let operand = function
  | Reg r -> register64 r
  | Spilled fs -> assert false

let binop_to_64 = function
  | Mmov -> movq
  | Madd -> addq
  | Msub -> subq
  | Mmul -> imulq
  | Mdiv -> idivq
  | Msete -> sete
  | Msetne -> setne
  | Msetl -> setl
  | Msetle -> setle
  | Msetg -> setg
  | Msetge -> setge

let ubranch_to_64 = function
  | Mjz -> jz
  | Mjnz -> jnz
  | Mjlei i -> assert false
  | Mjgi i -> assert false

let bbranch_to_64 = function
  | Mjl -> assert false
  | Mjle -> assert false

let rec lin (g:Ltltree.cfg) l =
  if not (Hashtbl.mem visited l) then (
    Hashtbl.add visited l ();
    instr g l (Label.M.find l g)
  )
  else (
    need_label l;
    emit_wl (jmp (l :> string))
  )

and instr g l = function
  | Ltltree.Econst (n, r, l1) ->
    emit l (movq (imm32 n) (operand r)); lin g l1
  | Ltltree.Ereturn ->
    emit l ret
  | Ltltree.Emunop (op, r, l1) ->
    let r64 = operand r in
    emit l (
      match op with
      | Maddi i ->
        addq i r64
      | Msetei i -> emit_wl (cmpq i r64);
        sete r64
      | Msetnei i -> emit_wl (cmpq i r64);
        setne r64
    );
    lin g l1
  | Ltltree.Embinop (op, r1, r2, l1) ->
    let r64_1, r64_2 = (operand r1), (operand r2) in
    emit l (
      match op with
      | Mmov | Madd | Msub | Mmul ->
        (binop_to_64 op) r64_1 r64_2
      | Mdiv ->
        idivq r64_1
      | Msete | Msetne | Msetl | Msetle | Msetg | Msetge ->
        emit_wl (cmpq r64_1 r64_2);
        (binop_to_64 op) r64_2
    );
    lin g l1
  | Ltltree.Eload (r_p1, n, r_p2, l1) ->
    emit l (movq (ind n (register64 r_p1)) (register64 r_p2)); lin g l1
  | Ltltree.Estore (r_p1, r_p2, n, l1) ->
    emit l (movq (register64 r_p2) (ind n (register64 r_p2)) ); lin g l1
  | Ltltree.Egoto (l1) ->
    if Hashtbl.mem visited l1 then (
      emit l (jmp l1); need_label l1
    ) else
      lin g l1
  | Ltltree.Epop (r_p, l1) ->
    emit l (popq (register64 r_p)); lin g l1
  | Ltltree.Epush (r, l1) ->
    emit l (pushq (operand r)); lin g l1
  | Ltltree.Emubranch (br, r, lt, lf) ->
    let r64 = operand r in
    emit_wl (
      match br with
      | Mjz | Mjnz ->
        testq r64 r64
      | Mjlei i | Mjgi i ->
        cmpq i r64
    );
    lin g l1

  | Ltltree.Embbranch (n, r1, r2, lt, lf) ->
    emit l (movq (imm32 n) (operand r)); lin g l1
  | Ltltree.Ecall (id, label) ->
    assert false
  | _ -> assert false

