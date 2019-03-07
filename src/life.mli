type live_info = {
          instr: Ertltree.instr;
          succ: Label.t list;    (* successeurs *)
  mutable pred: Label.set;       (* prédécesseurs *)
          defs: Register.set;    (* définitions *)
          uses: Register.set;    (* utilisations *)
  mutable  ins: Register.set;    (* variables vivantes en entrée *)
  mutable outs: Register.set;    (* variables vivantes en sortie *)
}

val liveness: Ertltree.cfg ->  (Label.t,  live_info) Hashtbl.t

val print_li: Format.formatter -> live_info -> unit

val print_with_liveness: Format.formatter -> Ertltree.file -> unit
