import Aoc.Utils
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

def add_neighbors (f : Field) (g : Game) (graph : Graph) : Graph := 
  let i := f.i
  let j := f.j
  let graph := add_neighbor f (i - 1) j g graph d_one -- north
  let graph := add_neighbor f (i + 1) j g graph d_one -- south
  let graph := add_neighbor f i (j - 1) g graph d_one -- west
  let graph := add_neighbor f i (j + 1) g graph d_one -- east
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

def solve_1_2 (s : String) (n m : Nat) : IO Unit := do
  IO.println s!"Input:\n{s}"
  match parse_game s |>.run {n := n, m := m} with
  | Except.error e => 
    IO.println s!"Error: {e}"
  | Except.ok g =>
    let graph : Graph := Std.HashMap.empty
    let ranges := cartesian_pairs (range_fin g.n) (range_fin g.m) 
    let graph : Graph := ranges.foldl (
      λgraph (i, j) => 
        let f := g.fields.get_value i j
        add_neighbors f g graph
    ) graph
    let starts := extract_fields g 
      |>.toList
      |>.filter (λf => get_val f == 0)
    let all_paths := starts.map (λf => find_path f graph) 
    let scores := all_paths.map (λp => get_score_trailheads p)
    IO.println s!"Solution 1: {scores.foldl (· + ·) 0}"

    -- solve 2
    let paths := all_paths.map (λp => get_hiking_rails p)
    let score := paths.map (λp => p.length) |>.foldl (· + ·) 0
    IO.println s!"Solution 2: {score}"
   

def main : IO Unit := do
  let input ← read_file "day10/input.txt"
  solve_1_2 input 41 41


-- tests

def test_data := "89010123
78121874
87430965
96549874
45678903
32019012
01329801
10456732"

def test : IO Unit := do
  solve_1_2 test_data 8 8

/- #eval test -/

def v1 : Vec 2 Nat := ⟨#[1, 2], by decide⟩
def v2 : Vec 2 Nat := ⟨#[1, 2], by decide⟩
def M1 : Matrix 2 2 Nat := ⟨#[v1, v2], by decide⟩

/- #eval range_fin 2 |>.map (λi => M1.gett i) -/
/- #eval cartesian_pairs (range_fin 2) (range_fin 2) -/ 
/-   |>.map (λ(i, j) => M1.get_value i j) -/

