import Aoc.Utils
import Std

structure Field where
  i : Nat
  j : Nat
  c : Char
deriving Repr

instance : ToString Field where
  toString x := s!"Field(i={x.i}, j={x.j}, c={x.c})"

abbrev Vec (n : Nat) (a : Type) := { ls : Array a // ls.size = n }

-- allow clean indexing into `Vec`'s; see Davids book
abbrev Vec.inBounds (vec : Vec n α) (i : Nat) : Prop :=
  i < vec.val.size

def Vec.get (vec : Vec n α) (i : Nat) (ok : vec.inBounds i) : α :=
  vec.val.get ⟨i, ok⟩

def Vec.get? (vec : Vec n α) (i : Nat) : Option α := 
  vec.val.get? i

def getElem {n : Nat} {a : Type} (v : Vec n a) (i : Fin n) : a :=
  v.val[i]

instance : GetElem (Vec n α) Nat α Vec.inBounds where
  getElem := Vec.get


abbrev Matrix (n m : Nat) (a : Type) := Vec n (Vec m a)

structure Game where
  n : Nat
  m : Nat
  fields: Matrix n m Field --Vec n (Vec m Field)
deriving Repr

def show_game_field (g : Game) := 
  let fields := g.fields.val.map (
    fun row => row.val.map (fun f => f.c.toString) |>.toList |> String.join
  ) |>.toList
  s!"{String.intercalate "\n" fields}"

instance : ToString Game where
  toString game := show_game_field game

instance : BEq Field where
  beq := fun f1 f2 => f1.i == f2.i && f1.j == f2.j && f1.c == f2.c

structure Config where
  n : Nat
  m : Nat

def build_mat (mat : List (List Field)) : ReaderT Config (Except String) Game := do
  let conf ← read
  let n := conf.n
  let m := conf.m
  let arr := mat.map (fun row => row.toArray) |>.toArray
  let p1 : Array (Option (Vec m Field)) := arr.map (
    fun row => 
      if h1 : row.size = conf.m then
        pure ⟨row, h1⟩
      else
        none
  )
  let p2 := p1.filterMap id
  if h2 : p2.size = n then
    let arr : Vec n (Vec m Field) :=  ⟨p2, h2⟩
    pure {n := n, m := m, fields := arr : Game}
  else
    throw "Failed building arrrix"

def get_field (mat : Matrix n m Field) (i j : Nat) : Option Field := 
  mat.get? i >>= fun row => row.get? j

def get_field_mat (mat : Matrix n m Field) (i j : Nat) : Option Field := 
  if h1 : mat.inBounds i  then 
    let row := mat.get i h1
    if h2 : row.inBounds j then 
      let field := row.get j h2
      some field
    else none
  else none


def split_data (s : String) : List (List Field) := 
  s.splitOn "\n" 
    |>.zip (List.range s.length)
    |>.map (fun (line, i) => (line.toList.zip (List.range line.length), i))
    |>.map (fun (line, i) => line.map (fun (c, j) => {i := i, j := j, c := c : Field}))

def parse_game (s : String) : ReaderT Config (Except String) Game := do
  build_mat (split_data s)

def update_field (mat : Matrix n m Field) (i j : Nat) (val : Char) := 
  if h1 : mat.inBounds i  then 
    let row := mat.get i h1
    if h2 : row.inBounds j then 
      let field := row.get j h2
      let new_field := {field with c := val}
      have : row.val.size = m := by
        apply row.property
      let updated_row : Vec m Field := 
        ⟨row.val.set ⟨j, h2⟩ new_field, by simp[*]⟩
      have : mat.val.size = n := by apply mat.property
      let updated_mat : Matrix n m Field := 
        ⟨mat.val.set ⟨i, h1⟩ updated_row, by simp[*]⟩
      pure updated_mat 
    else none
  else none

/-
Lab guards in 1518 follow a very strict patrol protocol which involves
repeatedly following these steps:

- If there is something directly in front of you, turn right 90 degrees.
- Otherwise, take a step forward.
-/

inductive GuardDirection
| North
| East
| South
| West
deriving Repr, Hashable

instance : BEq GuardDirection  where
  beq := fun x y => match x, y with
  | GuardDirection.North, GuardDirection.North => true
  | GuardDirection.East, GuardDirection.East => true
  | GuardDirection.South, GuardDirection.South => true
  | GuardDirection.West, GuardDirection.West => true
  | _, _ => false

inductive IncrementResult
| Blocked
| OutOfBounds
| Ok
deriving Repr

instance : ToString GuardDirection where
  toString x := match x with
  | GuardDirection.North => "North"
  | GuardDirection.East => "East"
  | GuardDirection.South => "South"
  | GuardDirection.West => "West"

instance : ToString IncrementResult where
  toString x := match x with
  | IncrementResult.Blocked => "Blocked"
  | IncrementResult.OutOfBounds => "OutOfBounds"
  | IncrementResult.Ok => "Ok"

abbrev NextPos := Int × Int

structure GameBoard where
  game : Game
  direction : GuardDirection
  prev_direction : GuardDirection := direction
  position : Field
  next_position : Field := position -- NOTE: (0 - 1 : Nat) = 0 🫠
deriving Repr


def update_field_game (i j : Nat) (c : Char) : StateM GameBoard Unit := do
  let board ← get
  let fields := update_field board.game.fields i j c
  match fields with
  | some x => set {board with game.fields := x}
  | none => pure ()

def update_guard_direction (dir : GuardDirection) : StateM GameBoard Unit := do
  let board ← get
  let pos := board.position
  let new_fig : Char := match dir with 
  | .North => '>'
  | .East => 'v'
  | .South => '<'
  | .West => '^'
  update_field_game pos.i pos.j new_fig

def update_field_game_dir (pos : Field)  : StateM GameBoard Unit := do
  let board ← get
  let dir := board.direction
  let prev_dir := board.prev_direction
  let field_val := match pos.c, dir, prev_dir with
  -- can only turn right
  | _, .East, .North => '+'
  | _, .West, .South => '+'
  | _, .South, .East => '+'
  | _, .North, .West => '+'
  -- initial
  | '.', .North, .North => '|'
  | '.', .East, .East => '-'
  | '.', .South, .South => '|'
  | '.', .West, .West => '-'
  | '-', .North, _ => '+'
  | '-', .South, _ => '+'
  | '|', .East, _ => '+'
  | '|', .West, _ => '+'
  | '^', .North, _ => '|'  -- initial
  | _, _, _ => 'G'
  update_field_game pos.i pos.j field_val


def increment_game : StateM GameBoard IncrementResult := do
  let board ← get
  let pos := board.position
  let dir := board.direction
  let fields := board.game.fields

  let next_pos : NextPos := match dir with -- board is matrix; (i, j) pos
  | .North => (pos.i - 1, pos.j)
  | .East => (pos.i, pos.j + 1)
  | .South => (pos.i + 1, pos.j)
  | .West => (pos.i, pos.j - 1)

  if next_pos.fst ≥ board.game.n
    || next_pos.snd ≥ board.game.m 
    || next_pos.fst < 0
    || next_pos.snd < 0 then
    update_field_game_dir pos
    pure IncrementResult.OutOfBounds
  else
    -- doesn't need to be an option here if we provide evidence
    let next_field := get_field_mat fields next_pos.fst.toNat next_pos.snd.toNat
    match next_field with
    | none => pure IncrementResult.OutOfBounds
    | some next_field =>
    if "#O".contains next_field.c then
      let next_dir := match dir with 
      | .North => .East
      | .East => .South
      | .South => .West
      | .West => .North
      modify fun board => {board with 
        direction := next_dir, 
        prev_direction := dir, 
        next_position := next_field}
      update_field_game_dir pos
      pure IncrementResult.Blocked
    else
      -- note: if we set {board with ...} then we use the non-updated board!
      modify fun board => {board with 
        next_position := next_field,
        position := next_field,
        prev_direction := dir
      }
      update_field_game_dir pos
      pure IncrementResult.Ok


def find_start (game : Game) := 
  -- Game starts facing up
  game.fields.val.map (fun row => row.val.map (·)) 
    |>.flatten 
    |>.find? (fun f => f.c == '^')

def count_field (game : Game) := 
  -- Game starts facing up
  game.fields.val.map (fun row => row.val.map (·)) 
    |>.flatten 
    |>.map (fun f => if "X|-+".contains f.c then 1 else 0)
    |>.foldl (· + ·) 0

def equal_coords (f1 f2 : Field) : Bool := 
  f1.i == f2.i && f1.j == f2.j

def extract_fields (game : Game) (exclude : Field) := 
  -- Game starts facing up
  let fields := game.fields.val.map (fun row => row.val.map (·)) 
    |>.flatten
  fields
    |>.filter (
      -- extract route excluding excluding starting field
      fun f => if "X|-+".contains f.c && ! equal_coords f exclude 
      then true else false
    )


def update_game : StateM GameBoard (Nat × IncrementResult) := do
  let mut i := 0
  let mut val := IncrementResult.Ok 
  while true do
    val ← increment_game
    match val with
    | IncrementResult.Ok => i := i + 1
    | IncrementResult.Blocked => i := i + 1
    | IncrementResult.OutOfBounds => break
  pure (i, val)

structure GameCycleResult where
  cycle : Bool
  result : IncrementResult
  iter : Nat
deriving Repr

def get_path (fields : Array Field) := 
  fields.map (fun f => (f.i, f.j))

def update_game_cycle (
  block_field : Field
) : StateM GameBoard GameCycleResult := do
  update_field_game block_field.i block_field.j 'O'
  let mut i := 0
  let mut cycle := false
  let mut val := IncrementResult.Ok 
  let mut visited_map : Std.HashMap (Nat × Nat × GuardDirection) Nat 
    := Std.HashMap.empty
  while true do
    val ← increment_game
    -- check visited twice moving in same direction
    let dir := (←get).direction
    let pos := (←get).position
    let value := visited_map.getD (pos.i, pos.j, dir) 0 
    if value == 0 then 
      visited_map := visited_map.insert (pos.i, pos.j, dir) 1
    else if value == 1 then
      visited_map := visited_map.insert (pos.i, pos.j, dir) 2
    else
      -- three times same spot
      visited_map := visited_map.insert (pos.i, pos.j, dir) 3
      cycle := true
    match val, cycle with
    | IncrementResult.Ok, false => i := i + 1
    | IncrementResult.Blocked, false => i := i + 1
    | IncrementResult.Blocked, true => break
    | IncrementResult.Ok, true => break
    | IncrementResult.OutOfBounds, _ => break
  pure {cycle := cycle, result := val, iter := i}


def print_res (final_gb : GameBoard) : IO Unit := do
  IO.println s!"Finished playing..."
  IO.println s!"{final_gb.game}"
  IO.println s!"\n... Final stats:"
  IO.println s!"{final_gb.direction}"
  IO.println s!"{final_gb.position}"

def solve_1 (game : Except String Game) : IO Unit := do
  match game with
  | Except.error e => 
    IO.println s!"Error: {e}"
  | Except.ok g => 
    match find_start g with
    | some c => 
      let gb : GameBoard 
        := {game := g, direction := GuardDirection.North, position := c}
      let (_, final_gb) := update_game |>.run gb
      IO.println s!"Solution 1: {count_field final_gb.game}"
      IO.println s!"Field: {final_gb.game}"
    | none => 
      IO.println "No start found"

def solve_2 (game : Except String Game) : IO Unit := do
  match game with
  | Except.error e => 
    IO.println s!"Error: {e}"
  | Except.ok g => 
    match find_start g with
    | some c => 
      let gb : GameBoard 
        := {game := g, direction := GuardDirection.North, position := c}
      IO.println s!"Starting game (s={gb.position})"
      let (_, final_gb) := update_game |>.run gb
      IO.println s!"\n\nFinding cycles..."
      let fields := extract_fields final_gb.game c
      let mut counter := 0
      let mut cycles := 0
      let total := fields.size
      for f in fields do
        let (i, _) := update_game_cycle ⟨f.i, f.j, '.'⟩ |>.run gb
        counter := counter + 1
        if counter % 50 == 0 then
          IO.println s!"Progress: {counter}/{total}"
          IO.println s!"Cycles found so far: {cycles}"
        if i.cycle then
          cycles := cycles + 1
      IO.println s!"Solution 2: {cycles}"
    | none => 
      IO.println "No start found"

def main : IO Unit := do
  let file ← read_file "day6/input.txt"
  let game :=  parse_game file |>.run {n := 130, m := 130}
  solve_1 game
  solve_2 game

-- tests
/- def teststr := "....#..... -/
/- .........# -/
/- .......... -/
/- ..#....... -/
/- .......#.. -/
/- .......... -/
/- .#..^..... -/
/- ........#. -/
/- #......... -/
/- ......#..." -/

/- def test_game : IO Unit := do -/
/-   let game :=  parse_game teststr |>.run {n := 10, m := 10} -/
/-   match game with -/
/-   | Except.error e => -/ 
/-     IO.println s!"Error: {e}" -/
/-   | Except.ok g => -/ 
/-     match find_start g with -/
/-     | some c => -/ 
/-       let gb : GameBoard -/ 
/-         := {game := g, direction := GuardDirection.North, position := c} -/
/-       IO.println s!"Starting game (s={gb.position})" -/
/-       let (i, final_gb) := update_game |>.run gb -/
/-       print_res final_gb -/
/-       IO.println s!"Num updates: {i}" -/
/-     | none => -/ 
/-       IO.println "No start found" -/
