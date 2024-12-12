import Aoc.Utils
import Aoc.Graph

def construct_mat_graph (n m: Nat) (filler : α) : Matrix n m α := 
  ⟨
  Array.range n |>.map (
    λ_ => ⟨List.replicate m filler |>.toArray, by simp⟩
  ),
  by simp
  ⟩

def mat_to_str (mat : Matrix n m Char) := 
  let fields := mat.val.map (
    fun row => row.val.map (fun f => f.toString) |>.toList |> String.join
  ) |>.toList
  s!"{String.intercalate "\n" fields}"

def get_fence_str (traced : List Field) (n m : Nat) : String :=
  -- Fence is on expanded grid by + 1
  let n := n + 1
  let m := m + 1
  let mat := construct_mat_graph n m '.'
  let mat := traced.foldl (
    λmat f => 
      if hi : f.i < n then
        if hj : f.j < m then
          mat.update_value ⟨f.i, hi⟩ ⟨f.j, hj⟩ 'f'
        else
        mat
      else
      mat
  ) mat
  mat_to_str mat

def direction (f1 f2 : Field) : Char := 
  let (i1, j1) := (f1.i, f1.j)
  let (i2, j2) := (f2.i, f2.j)
  if i1 == i2 && j1 < j2 then
    '→'
  else if i1 < i2 && j1 == j2 then
    '↓'
  else if i1 == i2 && j1 > j2 then
    '←'
  else
    '↑'

def get_fence_str2 (fence : List Edge) (n m : Nat) := 
  let fence_fields := fence.map (edge_to_fields)
    |>.map (
      λ(f1, f2) => 
        let dir := direction f1 f2
        [
        {f1 with c := dir},
        {f2 with c := dir}
      ]
    )
    |>.join
  let n := n + 1
  let m := m + 1
  let mat := construct_mat_graph n m '.'
  let mat := fence_fields.foldl (
    λmat f => 
      if hi : f.i < n then
        if hj : f.j < m then
          mat.update_value ⟨f.i, hi⟩ ⟨f.j, hj⟩ f.c
        else
        mat
      else
      mat
  ) mat
  mat_to_str mat

abbrev Visited := Std.HashSet Field
abbrev VisitedEdges := Std.HashSet (Field × Field)

def init_visited : Visited :=  
  Std.HashSet.empty

abbrev DFG := 
  ReaderT Graph (StateM Visited) (List Field)

partial def dfg_helper  (node : Field) (component : List Field) 
  (node_counter : Int) : DFG := do
  let g ← read
  let visited ← get
  if visited.contains node then
    pure []
  else do
    modify (fun visited => visited.insert node)
    let neighbors := g.getD node []
    let new_count := node_counter - 1
    if neighbors.all (λn => visited.contains n) then
      pure (node :: component)
    else
    neighbors.foldlM (
      λacc v =>  do
        let x ← dfg_helper v (component) new_count
        pure (acc ++ x)
    ) [node]

def find_components (fields : List Field) 
  : ReaderT Graph (StateM Visited) (List (List Field)) := 
  fields.mapM (
    λf => dfg_helper f [] fields.length
  )

def print_components (components : List (List Field)) := 
  for c in components do
    for f in c do
      IO.println s!"{f}"
    IO.println s!"\n"

def expand_edges (f : Field) : List Edge := 
  let i := f.i
  let j := f.j
  let edges : List Edge := [
    ⟨(i, j), (i, j + 1)⟩, -- → 
    ⟨(i, j + 1), (i + 1, j + 1)⟩, -- ↓
    ⟨(i + 1, j + 1), (i + 1, j)⟩, -- ←
    ⟨(i + 1, j), (i, j)⟩, -- ↑
  ]
  edges

def print_graph (graph : Graph):= 
  for k in graph.keys do
    for v in graph.getD k [] do
      IO.println s!"{k} -> {v}"

def compute_fences (component : List Field) : List Edge := 
  let expanded_edges := component.map (λf => expand_edges f) 
    |>.join
  let perimeter := expanded_edges.filter (λe => expanded_edges.count e == 1)
  perimeter 


abbrev Nodes := Std.HashSet Field

structure GraphWrap where
  prev: Field  -- Previous node (for counting turns)
  node: Field  -- Current node
  graph : Graph
  visited : Std.HashSet Field
  visited_edges : Std.HashSet Edge
  nodes : Nodes
  path : List Field
  paths : List (List Field) := []
  start_path : Field
  turns : Nat := 0
  counter : Nat := 0
deriving Repr

abbrev DFGSimple := 
  ReaderT Graph (StateM (Field × Visited × Nodes × (List Field))) Unit 

abbrev DFGG := 
  StateM GraphWrap Unit 

def pop (nodes : Nodes) : Option (Field) :=
  match nodes.toList.head? with
  | some x => pure x
  | none => none

def pop_node (node : Field) : StateM GraphWrap (Option Field) := do
  let g :=  (←get).graph
  let neighbors := g.getD node []
  match neighbors.getLast? with 
  | some n => 
    let neighbors := neighbors.dropLast
    let g := g.insert node neighbors
    modify (λc => {c with graph := g})
    pure (some n)
  | none => pure none

def assess_turn (prev next : Field) : StateM GraphWrap Nat := do
  let turn := next.i ≠ prev.i 
    && next.j ≠ prev.j 
    && (←get).counter != 0
  /- dbg_trace s!"Prev: {prev}; Current {(←get).node}; Next: {next}; {turn}" -/
  let increment := if turn then 1 else 0
  pure increment

abbrev Node := (Nat × Nat)

structure UGraph where
  nodes : List Field
  edges : List Edge
  map : Std.HashMap Field (List Field)
deriving Repr


def construct_ugraph (edges : List Edge) : UGraph :=
  let all_edges := edges.map (
    λe => [e, {src := e.dst, dst := e.src : Edge}]
  ) |> List.join
  let graph : Std.HashMap Field (List Field) := Std.HashMap.empty
  let graph := all_edges.foldl (
    λacc e => 
      let (src, dst) := (e.src, e.dst)
      let v1 : Field := ⟨src.fst, src.snd, 'v'⟩
      let v2 : Field := ⟨dst.fst, dst.snd, 'v'⟩
      let ns := acc.getD v1 []
      acc.insert v1 (ns.insert v2)
  ) graph
  let nodes := graph.keys
  ⟨nodes, edges, graph⟩

def get_neighbor_edge (node : Field) : StateM GraphWrap (Option Field) := do
  let g :=  (←get).graph
  let neighbors := g.getD node []
  let ve := (←get).visited_edges
  let next := neighbors.find? (
    λnext => 
      let edge : Edge := ⟨(node.i, node.j), (next.i, next.j)⟩
      !ve.contains edge
  )
  pure next

partial def traverse_simple : DFGG := do
  let node := (←get).node
  let next ← get_neighbor_edge node
  let nodes := (←get).nodes.erase node
  match next with
  | none => 
    match pop (←get).nodes with 
    | some popped_node => 
      let increment := if (←get).turns % 2 == 1 then 1 else 0
      modify (
        λc => {
          -- new path
          c with node := popped_node, prev := node, nodes := nodes, turns := c.turns + increment, start_path := popped_node, paths := c.paths.insert c.path, path := []
        }
      )
      traverse_simple 
    | none => 
      /- dbg_trace s!"Path (none next): traced {(←get).path}" -- Debug print -/
      let increment := if (←get).turns % 2 == 1 then 1 else 0
      modify (
        λc => {c with turns := c.turns + increment }
      )
      /- dbg_trace s!"No neighbors; No more pop" -/
      pure ()
  | some next => 
  let edge : Edge := ⟨(node.i, node.j), (next.i, next.j)⟩
  let increment ← assess_turn (←get).prev next
  modify (
    λc =>  {
    c with node := next, prev := node, visited := (c.visited.insert node), path := c.path ++ [node], nodes := nodes, turns := c.turns + increment, counter := c.counter + 1, visited_edges := c.visited_edges.insert edge}
  )
  traverse_simple 

def get_start_node (graph : Std.HashMap Field (List Field)) := 
  -- Find node with the most neighbors
  let start_node := graph.keys.map (
   λk => (k, graph.getD k [] |>.length)
  )  
  |>.foldl (
    λmax_pair pair => 
      if max_pair.snd < pair.snd then pair else max_pair
  ) ({i := 0, j := 0, c := 'v' : Field}, 0)
  start_node.fst


def turns_graph (edges : List Edge) : GraphWrap :=
  let visited := init_visited
  let ve : Std.HashSet Edge := Std.HashSet.empty
  let ug := construct_ugraph edges
  let nodes := ug.map.keys
  let nodes_set : Nodes := nodes.foldl (
    λacc k => acc.insert k
  ) Std.HashSet.empty
  let node := get_start_node ug.map
  let (_, gw) := traverse_simple
    |>.run {
      prev := node,
      node := node,
      start_path := node,
      graph := ug.map,
      visited := visited,
      visited_edges := ve,
      nodes := nodes_set,
      path := [],
      turns := 0,
    }  
  gw

def count_turns (edges : List Edge) := 
  turns_graph edges |>.turns

def price_fence (component : List Field) := 
  let area := component.length
  let num_fence := compute_fences component |>.length
  area * num_fence

def price_fence_second (component : List Field) := 
  let area := component.length
  let perimeter := compute_fences component
  let turns := count_turns perimeter
  dbg_trace s!"Turns: {turns}"
  -- dbg_trace s!"{get_fence_str2 perimeter 140 140}"
  area * turns

def solve (s : String) (n m : Nat) : IO Unit := do
  match parse_game s |>.run {n := n, m := m} with
  | Except.error e => 
    IO.println s!"Error: {e}"
  | Except.ok g =>
    let graph := build_graph_game g (fun f1 f2 => f1.c == f2.c)
    let nodes := extract_fields g |>.toList
    let (components, _) :=  find_components nodes 
      |>.run graph
      |>.run init_visited
    let components := components.filter (!·.isEmpty)

    let prices := components.map price_fence |>.foldl (· + ·) 0
    IO.println s!"Solution 1: {prices}"

    -- Second
    let out := components.map price_fence_second |>.foldl (· + ·) 0
    IO.println s!"Solution 2: {out}"


def main : IO Unit := do
  let file ← read_file "day12/input.txt"
  solve file 140 140


/- -- Tests -/

def test_str := "AAAA
BBCD
BBCC
EEEC"

def test_str2 := "OOOOO
OXOXO
OOOOO
OXOXO
OOOOO"

def test_str3 := "RRRRIICCFF
RRRRIICCCF
VVRRRCCFFF
VVRCCCJFFF
VVVVCJJCFE
VVIVCCJJEE
VVIIICJJEE
MIIIIIJJEE
MIIISIJEEE
MMMISSJEEE"

def test_str4 := "EEEEE
EXXXX
EEEEE
EXXXX
EEEEE"

def test_str5 := "AAAAAA
AAABBA
AAABBA
ABBAAA
ABBAAA
AAAAAA"

-- all passes
#eval "Test cases strings text:"
#eval solve test_str 4 4
#eval solve test_str2 5 5
#eval solve test_str3 10 10
#eval solve test_str4 5 5
#eval solve test_str5 6 6 

def edges_mobius : List Edge := [
  ⟨(0, 0), (0, 1)⟩,
  ⟨(1, 0), (0, 0)⟩,
  ⟨(0, 1), (0, 2)⟩,
  ⟨(0, 2), (0, 3)⟩,
  ⟨(0, 3), (0, 4)⟩,
  ⟨(1, 4), (1, 3)⟩,
  ⟨(0, 4), (0, 5)⟩,
  ⟨(1, 5), (1, 4)⟩,
  ⟨(0, 5), (0, 6)⟩,
  ⟨(0, 6), (1, 6)⟩,
  ⟨(1, 6), (2, 6)⟩,
  ⟨(2, 5), (1, 5)⟩,
  ⟨(2, 6), (3, 6)⟩,
  ⟨(3, 5), (2, 5)⟩,
  ⟨(3, 6), (4, 6)⟩,
  ⟨(3, 4), (3, 5)⟩,
  ⟨(3, 3), (3, 4)⟩,
  ⟨(4, 3), (3, 3)⟩,
  ⟨(5, 3), (4, 3)⟩,
  ⟨(4, 6), (5, 6)⟩,
  ⟨(5, 6), (6, 6)⟩,
  ⟨(6, 6), (6, 5)⟩,
  ⟨(6, 5), (6, 4)⟩,
  ⟨(6, 4), (6, 3)⟩,
  ⟨(5, 2), (5, 3)⟩,
  ⟨(6, 3), (6, 2)⟩,
  ⟨(5, 1), (5, 2)⟩,
  ⟨(6, 2), (6, 1)⟩,
  ⟨(6, 1), (6, 0)⟩,
  ⟨(6, 0), (5, 0)⟩,
  ⟨(4, 1), (5, 1)⟩,
  ⟨(5, 0), (4, 0)⟩,
  ⟨(3, 1), (4, 1)⟩,
  ⟨(4, 0), (3, 0)⟩,
  ⟨(3, 0), (2, 0)⟩,
  ⟨(3, 2), (3, 1)⟩,
  ⟨(2, 3), (3, 3)⟩,
  ⟨(3, 3), (3, 2)⟩,
  ⟨(1, 3), (2, 3)⟩,
  ⟨(2, 0), (1, 0)⟩
]

def edge_simple :  List Edge := [
  ⟨(0, 0), (0, 1)⟩,
  ⟨(0, 1), (1, 1)⟩,
  ⟨(1, 1), (1, 0)⟩,
  ⟨(1, 0), (0, 0)⟩,
]

def edge_simple2 :  List Edge := [
  ⟨(0, 0), (0, 1)⟩,
  ⟨(0, 1), (0, 2)⟩,
  ⟨(0, 2), (1, 2)⟩,
  ⟨(1, 2), (1, 1)⟩,
  ⟨(1, 1), (2, 1)⟩,
  ⟨(2, 1), (2, 0)⟩,
  ⟨(2, 0), (1, 0)⟩,
  ⟨(1, 0), (0, 0)⟩,
]

def test_set := 
  let e1 := Edge.mk (1, 2) (3, 4)
  let e2 := Edge.mk (3, 4) (1, 2)
  e1 == e2

def test_set2 := 
  let s : Std.HashSet Edge := Std.HashSet.empty
  let s := s.insert (Edge.mk (1, 2) (3, 4))
  s.contains (Edge.mk (3, 4) (1, 2))

#eval "Test cases turns:"
#eval count_turns edges_mobius
#eval count_turns edge_simple2
#eval count_turns edge_simple

#eval construct_ugraph edge_simple |>.map |>  get_start_node
#eval construct_ugraph edges_mobius |>.map |>  get_start_node
#eval test_set
#eval test_set2
