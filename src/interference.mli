type arcs = {
  mutable prefs: Register.set;
  mutable intfs: Register.set
}

type igraph = arcs Register.map

val make: (Label.t, Life.live_info) Hashtbl.t -> igraph

val print_file: Format.formatter -> Ertltree.file -> unit
