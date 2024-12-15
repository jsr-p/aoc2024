import Aoc.Matrix

def hash_field (f: Field) : UInt64 := 
  mixHash (hash f.i) (hash f.j)

instance : Hashable Field where
  hash := hash_field

def is_inside_field (i j : Int) (n m : Nat) : Option (Fin n × Fin m) := 
  if _ : i ≥ 0 then
    if _ : j ≥ 0 then
      let i_pos := i.toNat
      let j_pos := j.toNat
      if hi1 : i_pos < n then
        if hj1 : j_pos < m then
          some (⟨i_pos, hi1⟩, ⟨j_pos, hj1⟩)
        else none
      else none
    else none
  else none

structure Neighbors where
  north : Option Field
  south : Option Field
  east : Option Field
  west : Option Field
deriving Repr

abbrev Graph := Std.HashMap Field (List Field)

def get_val (f : Field) : Nat := 
  f.c.toString.toNat!

def d_one (f neigh : Field) : Bool := 
  let topo1 := get_val f
  let topo2 := get_val neigh 
  if topo2 - topo1 == 1 then
    true
  else false

def add_neighbor (f : Field) (i j : Int) (g : Game) (graph : Graph)
  (condition : Field → Field → Bool): Graph := 
  match is_inside_field i j g.n g.m with 
  | some (fin_i, fin_j) => 
    let neighbor := g.fields.get_value fin_i fin_j
    if condition f neighbor then
      let ns := graph.getD f []
      graph.insert f (neighbor :: ns)  -- prepend neighbor
    else graph
  | none => graph

def add_neighbors 
(f : Field) (g : Game) (graph : Graph)
(condition : Field → Field → Bool)
: Graph := 
  let i := f.i
  let j := f.j
  let graph := add_neighbor f (i - 1) j g graph condition -- north
  let graph := add_neighbor f (i + 1) j g graph condition -- south
  let graph := add_neighbor f i (j - 1) g graph condition -- west
  let graph := add_neighbor f i (j + 1) g graph condition -- east
  graph


partial def find_paths_helper 
  (f: Field) (graph : Graph) (visited : List (List Field)) := 
  match graph.getD f [] with
  | [] => visited.map (λv => f :: v)
  | neighbors => 
    neighbors.foldl
      (
        -- concat all paths branching out from each neighbor n;
        -- List (List Field) ++ List (List Field) where each List Field
        -- a path
        fun acc n =>
          acc ++ find_paths_helper n graph (visited.map (λv => f :: v))
      )
      []
    
partial def find_path (f: Field) (graph : Graph) :=
  find_paths_helper f graph [[]]


def get_trailheads (paths : List (List Field)) := 
  paths
    -- need to end in a 9
    |>.filter (λl => l.any (λf => get_val f == 9))
    |>.map (
    λl => l.reverse |>.getLast?
    )  
    |>.reduceOption
    |>.eraseDups

def get_hiking_rails (paths : List (List Field)) := 
  paths
    -- need to end in a 9
    |>.filter (λl => l.any (λf => get_val f == 9))


def get_score_trailheads (paths : List (List Field)) := 
  get_trailheads paths |> List.length

def init_graph : Graph := 
  Std.HashMap.empty

def build_graph_game (g : Game) (condition : Field → Field → Bool) : Graph := 
  let graph := init_graph
  let ranges := cartesian_pairs (range_fin g.n) (range_fin g.m) 
  let graph : Graph := ranges.foldl (
    λgraph (i, j) => 
      let f := g.fields.get_value i j
      add_neighbors f g graph condition
  ) graph
  graph


structure Edge where
  src : (Nat × Nat)
  dst : (Nat × Nat)
deriving Repr, BEq, Hashable

instance : BEq Edge where  -- Undirected graph
  beq := fun e1 e2 => 
    (e1.src == e2.src && e1.dst == e2.dst)
    ||
    (e1.src == e2.dst && e1.dst == e2.src)

def hash_edge (e: Edge) : UInt64 := 
  let h1 := hash e.src
  let h2 := hash e.dst
  let hm1 := mixHash h1 h2
  let hm2 := mixHash h2 h1
  mixHash hm1 hm2

instance : Hashable Edge where
  hash :=  fun e => 
    let (h1, h2) := (hash e.src, hash e.dst)
    mixHash (min h1 h2) (max h1 h2)

instance : Hashable Field where
  hash := hash_field

instance : ToString Edge where
  toString e := s!"Edge({e.src}, {e.dst})"

-- Plotting utils

def edge_to_fields (edge : Edge) (arrow : Bool := false) : Field × Field := 
  let src := edge.src
  let dst := edge.dst
  let (i1, j1) := src
  let (i2, j2) := dst
  if arrow then
    let c := if i1 == i2 && j1 < j2 then
      '→'
    else if i1 < i2 && j1 == j2 then
      '↓'
    else if i1 == i2 && j1 > j2 then
      '←'
    else
      '↑'
    (⟨src.fst, src.snd, c⟩, ⟨dst.fst, dst.snd, c⟩)
  else 
    let c := 'f'
    (⟨src.fst, src.snd, c⟩, ⟨dst.fst, dst.snd, c⟩)


def plot_fence (fence : List Edge) (n m : Nat) : IO Unit := do
  -- Fence is on expanded grid by + 1
  let n := n + 1
  let m := m + 1
  let ranges : List Field := cartesian_pairs (range_fin n) (range_fin m)
    |>.map (λ(f1, f2) => ⟨f1.val, f2.val, '.'⟩)
  let rs := reshape n m ranges
  let g := build_mat rs |>.run {n := n, m := m}
  match g with 
  | Except.error e => 
    IO.println s!"Error: {e}"
  | Except.ok game =>
    let fence_fields := fence.map (edge_to_fields)
      |>.map (λ(f1, f2) => [f1, f2])
      |>.join
    let game := fence_fields.foldl (
      λg f => 
        if hi : f.i < g.n then
          if hj : f.j < g.m then
            {
              g with fields := g.fields.update_value ⟨f.i, hi⟩ ⟨f.j, hj⟩ f
            }
          else
          g
        else
        g
    ) game
    IO.println s!"{game}"  


def plot_component (component : List Field) (n m : Nat) : IO Unit := do
  let ranges : List Field := cartesian_pairs (range_fin n) (range_fin m)
    |>.map (λ(f1, f2) => ⟨f1.val, f2.val, '.'⟩)
  let rs := reshape n m ranges
  let g := build_mat rs |>.run {n := n, m := m}
  match g with 
  | Except.error e => 
    IO.println s!"Error: {e}"
  | Except.ok game =>
    let game := component.foldl (
      λg f => 
        if hi : f.i < g.n then
          if hj : f.j < g.m then
            {
              g with fields := g.fields.update_value ⟨f.i, hi⟩ ⟨f.j, hj⟩ f
            }
          else
          g
        else
        g
    ) game
    IO.println s!"{game}"  


def construct_edge_graph (edges : List Edge) :=
  let graph := init_graph
  let graph : Graph := edges.foldl (
    λacc e => 
      let (f1, f2) := edge_to_fields e
      let ns := acc.getD f1 []
      acc.insert f1 (ns.insert f2)
  ) graph
  graph


abbrev GraphSimple := Std.HashMap Field Field
def init_graph_simple : GraphSimple := Std.HashMap.empty

def construct_edge_graph_simple (edges : List Edge) :=
  let graph := init_graph_simple 
  let graph : GraphSimple := edges.foldl (
    λacc e => 
      let (f1, f2) := edge_to_fields e
      acc.insert f1 f2
  ) graph
  graph
