type arcs = {
  mutable prefs: Register.set;
  mutable intfs: Register.set
}

type igraph = arcs Register.map

type color = Ltltree.operand

type coloring = color Register.map

val make: (Label.t, Life.live_info) Hashtbl.t -> igraph

val color: igraph -> coloring * int

val print_file: Format.formatter -> Ertltree.file -> unit
