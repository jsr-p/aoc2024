import Aoc.Utils
import Aoc.Matrix


def split_digit (d : Nat) := 
  let s := s!"{d}"
  let l := s.length / 2
  let d1 := s.take l
  let d2 := s.drop l
  let d2 := d2.dropWhile (λc => c == '0') |> 
    (
      fun s => match s with 
      | "" => "0"
      | _ => s
    )
  (d1.toNat!, d2.toNat!)


def insert_place_list (l : List α) (i : Nat)  (val : α) := 
    l.take i ++ [val] ++ l.drop i

def update_stone (line : List Nat) (i : Nat) : (List Nat) × Nat := 
  let stone := line.get! i
  if stone == 0 then
    (line.set i 1, i + 1)
  else if s!"{stone}".length % 2 == 0 then  -- ok while digits single unicode points
    let (s1, s2) := split_digit stone
    let line := line.set i s1
    (insert_place_list line (i + 1) s2, i + 2)
  else 
    (line.set i (stone * 2024), i + 1)

def parse_line (s : String) : List Nat := 
  s.splitOn " " |>.filter (!·.isEmpty) |>.map (λs => s.trim.toNat!)

def update_line (line : List Nat) : List Nat := 
  let (line, _) := line.foldl (
    λ(l, n_idx) _ => update_stone l n_idx
  ) (line, 0)
  line

def update_stone_2 (stone : Nat) : (List Nat) := 
  if stone == 0 then
    [1]
  else if s!"{stone}".length % 2 == 0 then  -- ok while digits single unicode points
    let (s1, s2) := split_digit stone
    [s1, s2]
  else 
  [stone * 2024]


inductive BinTree (α : Type) where
  | leaf : BinTree α
  | branch : BinTree α → α → BinTree α → BinTree α
deriving Repr

instance : ToString (BinTree Nat) where
  toString tree := 
    let rec aux : BinTree Nat → String
      | BinTree.leaf => "leaf"
      | BinTree.branch l v r => 
        s!"(branch {aux l} {v} {aux r})"
    aux tree

def BinTree.count : BinTree α → Nat
  | .leaf => 0
  | .branch l _ r =>
    1 + l.count + r.count

def BinTree.count_lowest : BinTree α → Nat
  | .leaf => 0
  | .branch l _ r => 
    match l, r with
    | .leaf, .leaf => 1
    | _, _=> l.count_lowest + r.count_lowest

def some_tree : BinTree Nat := 
  -- hardcode tree
  BinTree.branch 
    (BinTree.branch BinTree.leaf 1 BinTree.leaf) 
    2 
    (BinTree.branch BinTree.leaf 3 BinTree.leaf)

def update_stone_3 (stone : Nat) : List Nat := 
  if stone == 0 then
    [1]
  else if s!"{stone}".length % 2 == 0 then  -- ok while digits single unicode points
    let (s1, s2) := split_digit stone
    [s1, s2]
  else 
  [stone * 2024]

structure Counter where
  count : Nat
  h0 : count ≥ 0
deriving Repr

instance : ToString Counter where
  toString c := s!"{c.count}"

def init_counter : Counter := 
  let count := 0
  have h0 : count ≥ 0 := by decide
  {count := count, h0 := h0}

def Counter.increment (c : Counter) : Counter := 
  let new_count := c.count + 1
  have h0 : new_count ≥ 0 := by
    apply Nat.le_add_left
  {count := new_count, h0}

def terminates (max_depth: Nat) (depth : Counter) (h0 : ¬depth.count ≥ max_depth)
  : max_depth - (depth.increment.count) < max_depth - depth.count:= 
  have hi := Nat.lt_of_not_ge h0
  have h : max_depth - (depth.increment.count) < max_depth - depth.count := by
      rw [Counter.count]
      apply Nat.sub_succ_lt_self
      assumption
  h

def grow_tree_helper 
  (stone : Nat) (so_far : BinTree Nat) (depth : Counter) (max_depth : Nat) := 
  if h0 : depth.count ≥ max_depth then
    so_far
  else
    have _ :=  terminates max_depth depth h0  -- for termination
    let next_depth := depth.increment
    match update_stone_2 stone with
    | [s] => 
      BinTree.branch 
      (grow_tree_helper s so_far next_depth max_depth) 
      stone 
      BinTree.leaf
    | [s1, s2] => (
      BinTree.branch 
      (grow_tree_helper s1 so_far next_depth max_depth) 
      stone 
      (grow_tree_helper s2 so_far next_depth max_depth)
    )
    | _ => so_far
termination_by max_depth - depth.count


def grow_pseudotree_helper 
  (stone : Nat) (depth : Counter) (max_depth : Nat)
  : StateM Nat Unit := 
  if h0 : depth.count ≥ max_depth then
    modify (λs => s + 1)
  else
    have _ :=  terminates max_depth depth h0  -- for termination
    let next_depth := depth.increment
    match update_stone_2 stone with
    | [s] => do
      let t1 ← grow_pseudotree_helper s next_depth max_depth 
      pure t1
    | [s1, s2] => 
      do 
      let _ ← grow_pseudotree_helper s1 next_depth max_depth 
      let t2 ← grow_pseudotree_helper s2 next_depth max_depth
      pure t2
    
    | _ => pure ()
termination_by max_depth - depth.count

def update_mttree_helper (stone : Nat) (tree : BinTree Nat) (depth : Nat) := 
  (
  BinTree.branch 
  tree
  stone 
  (grow_tree_helper stone BinTree.leaf init_counter depth) 
  )

def update_multiple_line_tree (line : List Nat) (depth : Nat := 3) : BinTree Nat := 
  let start_tree : BinTree Nat := BinTree.leaf
  line.foldl (
    λtree stone => update_mttree_helper stone tree depth
  ) start_tree 


def update_multiple_line_pseudotree 
  (line : List Nat) (iter : Nat := 3) := 
  line.foldlM (
    λ_ stone => 
      grow_pseudotree_helper stone init_counter iter
  ) ()


abbrev StoneMap := Std.HashMap (Nat × Nat) Nat

def init_stone_map : StoneMap := 
    Std.HashMap.empty

def update_stone_aux
  (stone : Nat) (depth : Counter) (max_depth : Nat)
  : StateM StoneMap Nat  := do
  let rel_depth := max_depth - depth.count
  let x := (←get).getD (stone, rel_depth) 0
  if x > 0 then
    pure x
  else if h0 : depth.count ≥ max_depth then
    pure 1
  else
    have _ :=  terminates max_depth depth h0  -- for termination
    let next_depth := depth.increment
    match update_stone_2 stone with
    | [s] => do
      let t1 ← update_stone_aux s next_depth max_depth 
      modify (λmap => map.insert (stone, rel_depth) t1)
      pure t1
    | [s1, s2] => 
      do 
      let t1 ← update_stone_aux s1 next_depth max_depth 
      let t2 ← update_stone_aux s2 next_depth max_depth 
      modify (λmap => map.insert (stone, rel_depth) (t1 + t2))
      /- modify (λmap => map.insert (s2, rel_depth) t2) -/
      pure (t1 + t2)
    
    | _ => pure 1
termination_by max_depth - depth.count


def update_multiple_stone 
  (line : List Nat) (max_depth : Nat := 3) : StateM StoneMap Nat := 
  line.foldlM (
    λacc stone => do
      let x ← update_stone_aux stone init_counter max_depth
      pure (acc + x)
  ) 0

def update_line_2 (line : List Nat) : List Nat := 
  let new_line := line.map (λstone => update_stone_2 stone)
  new_line.join

def update_line_helper (so_far : List Nat) : List Nat → List Nat
  | [] => so_far
  | x :: xs => 
    update_line_helper (so_far ++ update_stone_2 x) xs

def update_line_3 (line : List Nat) : List Nat := 
  let new_line := update_line_helper [] line
  new_line

def update_line_arr_helper
  (so_far : Array Nat) (orig : Array Nat) (i : Nat) : Array Nat := 
  if h : i < orig.size then 
    update_line_arr_helper (so_far ++ update_stone_2 orig[i]) orig (i + 1)
  else 
    so_far
termination_by orig.size - i

def update_line_arr (line : Array Nat) : Array Nat := 
  update_line_arr_helper #[] line 0

def update_line_multiple_arr (line : Array Nat) (iter : Nat) 
  (update_fn : Array Nat → Array Nat) : Array Nat := 
  let iters := Array.range iter
  iters.foldl (
    -- keep passing on updated Array
    λl _ => update_fn l
  ) line

def update_line_multiple (line : List Nat) (iter : Nat) 
  (update_fn : List Nat → List Nat) : List Nat := 
  let iters := List.range iter
  iters.foldl (
    λl _ => -- keep passing on updated list
      update_fn l
  ) line

def main (args : List String) : IO Unit := do
  let input ← read_file "day11/input.txt"
  let line :=  parse_line input
  match args with
  | [arg1, arg2] => 
    let iter := arg2.toNat!
    match arg1 with 
    | "tree" => 
      -- add 2 extra to get to same depth as array / list
      let out := update_multiple_line_tree line (iter + 2) |>.count_lowest
      IO.println s!"Solution 2: {out}"
    | "pseudotree" => 
      -- add 1 extra to get to same depth as array / list
      let (_, out) := update_multiple_line_pseudotree line (iter + 1) |>.run 0
      IO.println s!"Solution 2: {out}"
    | "stoneaux" => 
      let out := update_multiple_stone line iter |>.run init_stone_map |>.fst
      IO.println s!"Solution 2: {out}"
    | "list" => 
      let out := update_line_multiple line iter update_line_2
      IO.println s!"Solution 2: {out.length}"
    | "list-rec" =>  -- slow 
      let out := update_line_multiple line iter update_line_3
      IO.println s!"Solution 2: {out.length}"
    | "array" => 
      let out := update_line_multiple_arr line.toArray iter update_line_arr
      IO.println s!"Solution 2: {out.size}"
    | _ => IO.println s!"Invalid argument; {args}"
  | _ => IO.println s!"Invalid arguments"

-- tests
/- def test_str := "0 1 10 99 999" -/

/- def main : IO Unit := do -/
/-   let input ← read_file "day11/input.txt" -/
/-   let line :=  parse_line input -/
/-   let out := update_line_3 line -/
/-   let out := update_line_multiple_arr line.toArray 25 update_line_arr -/
/-   IO.println s!"{out.size}" -/

/- #eval test_multiple -/

/- def test2 := do -/
/-   let input ← read_file "day11/input.txt" -/
/-   let line :=  parse_line input -/
/-   IO.println s!"{line}" -/
/-   let out := update_line_multiple line 1 -/
/-   IO.println s!"{out}" -/

/- #eval test2 -/
/- #eval "1010".take 2 -/
/- #eval "1020".drop 2 -/
/- #eval split_digit 101020 -/
/- #eval split_digit 100020 -/
/- #eval split_digit 100000 -/

/- def test_seq : IO Unit := do -/
/-   let line :=  parse_line test_str -/ 
/-   IO.println s!"{out}" -/

/- #eval split_digit 10 -/
/- #eval solve_1 test_str -/
/- #eval solve_1 "125 17" -/
/- #eval update_stone [253000, 1, 7] 1 -/
/- #eval update_line [253000, 1, 7] -/
/- #eval update_line_multiple [125, 17] 6 -/

/- def t1 := -/ 
/-   let line :=  parse_line test_str -/ 
/-   let (s1, s2) := split_digit 10 -/
/-   let line := line.set 1 s1 -/
/-   (insert_place_list line (1 + 1) s2, 1 + 2) -/
/- #eval t1 -/

-- test tree

/- def l := [1, 2, 3] -/
/- def l := [125, 17] -/
/- def test : IO Unit := do -/
/-   let (_, out) :=  grow_pseudotree_helper 125 init_counter 6 |>.run 0 -/
/-   IO.println s!"{out}" -/

/- #eval update_multiple_line_tree l 6 |>.count_lowest -/
/- #eval test -/
/- #eval update_mttree_helper 125 BinTree.leaf 6 -/
/- #eval grow_tree_helper 125 BinTree.leaf init_counter 6 -/
/- #eval grow_pseudotree_helper 125 init_counter 6 |>.run 0 -/
/- def t (iter : Nat) : IO Unit := do -/
/-   let d :=  grow_pseudotree_helper_2 125 init_counter iter |>.run [] -/
/-   IO.println s!"{d.snd}" -/
/- #eval grow_tree_helper 125 BinTree.leaf init_counter 8 |>.count_lowest -/
/- #eval grow_pseudotree_helper 125 init_counter 30 |>.run 0 -/
/- #eval update_line_multiple [125] 8 update_line_2 |>.length -/
/- #eval update_multiple_line_pseudotree [125] 9 |>.run 0 -/ 
/- #eval t 4 -/

/- def gl := -/ 
/-   let start_tree : BinTree Nat := BinTree.leaf -/
/-   l.foldl ( -/
/-     λtree stone => BinTree.branch tree stone BinTree.leaf -/
/-   ) start_tree -/ 

/- #eval gl -/
/- #eval gl.count -/
/- #eval gl.count_lowest -/
/- /1- #eval gl2 40 |>.count_lowest -1/ -/
/- /1- #eval gl2 30 -1/ -/
/- /1- #eval gl2.count_lowest -1/ -/


/- def simulate_stone (iter : Nat) : IO Unit := do -/
/-   let mut val := [0] -/
/-   IO.println s!"{val}" -/
/-   for i in [1:iter] do -/
/-     val := update_line_multiple val 1 update_line_2 -/
/-     IO.println s!"{val}; count = {val.length}; iter={i}; maxdepth={iter}; r={iter - i}" -/


/- #eval update_stone_aux 0 init_counter 1 |>.run init_stone_map -/
/- #eval update_stone_aux 0 init_counter 2 |>.run init_stone_map -/
/- #eval update_stone_aux 0 init_counter 3 |>.run init_stone_map -/
/- #eval update_stone_aux 0 init_counter 4 |>.run init_stone_map -/
/- #eval update_stone_aux 0 init_counter 9 |>.run init_stone_map -/


/- #eval simulate_stone 10 -/
/- #eval simulate_stone 11 -/
/- #eval simulate_stone 12 -/
/- #eval simulate_stone 13 -/


/- def line := [125, 17] -/
/- def iter := 50 -/
/- #eval update_multiple_stone line (iter) |>.run init_stone_map -/
/- #eval update_line_multiple_arr line.toArray iter update_line_arr |>.size -/
