import Aoc.Utils

structure Field where
  i : Nat
  j : Nat
  c : Char
deriving Repr

instance : ToString Field where
  toString x := s!"Field(i={x.i}, j={x.j}, c={x.c})"

abbrev Vec (n : Nat) (a : Type) := { ls : List a // ls.length = n }

-- allow clean indexing into `Vec`'s; see Davids book
abbrev Vec.inBounds (vec : Vec n α) (i : Nat) : Prop :=
  i < vec.val.length

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

instance : ToString Game where
  toString game := s!"Game(n={game.n}, m={game.m})"

instance : BEq Field where
  beq := fun f1 f2 => f1.i == f2.i && f1.j == f2.j && f1.c == f2.c

structure Config where
  n : Nat
  m : Nat

def build_mat (mat : List (List Field)) : ReaderT Config (Except String) Game := do
  let conf ← read
  let n := conf.n
  let m := conf.m
  let p1 : List (Option (Vec m Field)) := mat.map (
    fun row => 
      if h1 : row.length = conf.m then
        pure ⟨row, h1⟩
      else
        none
  )
  let p2 := p1.filterMap id
  if h2 : p2.length = n then
    let mat : Vec n (Vec m Field) :=  ⟨p2, h2⟩
    pure {n := n, m := m, fields := mat : Game}
  else
    throw "Failed building matrix"


def get_field (mat : Matrix n m Field) (i j : Nat) : Option Field := 
  mat.get? i >>= fun row => row.get? j


def split_data (s : String) : List (List Field) := 
  s.splitOn "\n" 
    |>.zip (List.range s.length)
    |>.map (fun (line, i) => (line.toList.zip (List.range line.length), i))
    |>.map (fun (line, i) => line.map (fun (c, j) => {i := i, j := j, c := c : Field}))

def parse_game (s : String) : ReaderT Config (Except String) Game := do
  build_mat (split_data s)


def mat_indices (i j : Nat) := 
  List.range i |>.map (fun x => List.zip (List.replicate j x) (List.range j))

def parse_field (field : Field) := 
  Prod.mk field.i field.j

def rev_range (start stop : Nat) (zero_inc := true) := 
  -- note: equivalent to python range with step=-1;
  -- we include zero by default i.e. setting stop equal to -1 in python
  if zero_inc then
    if start == 0 then
      []
    else
      List.range (start + 1) |>.drop stop |>.reverse
  else
    List.range start |>.map (· + 1) |>.drop stop |>.reverse

def range (start stop : Nat) := 
  -- equivalent to python range with step=1
  List.range stop |>.drop start

def rep_vec (a : Nat) (n : Nat):= 
  List.replicate n a


structure Directions where
  N : String
  NE : String
  E : String
  SE : String
  S : String
  SW : String
  W : String
  NW : String
deriving Repr

def remove_leading_x (s : String) := 
  if s.startsWith "X" then
    s.drop 1
  else
    s

def extract_string_game (vi vj : List Nat) (game: Game) := 
  List.zip vi vj |>.map (fun (i, j) => 
    get_field game.fields i j
    >>= 
    fun field => field.c
    ) |>.foldl (
      fun acc optChar => 
        match optChar with
        | some c => acc.push c
        | none => acc
      ) "" |> remove_leading_x

def parse_routes (field : Field) (game : Game) : Directions := 
  let i := field.i
  let j := field.j
  let n := game.n
  let m := game.m
  {
    -- NORTH, NORTH EAST, EAST, SOUTH EAST, SOUTH, SOUTH WEST, WEST, NORTH WEST
    N := extract_string_game (rev_range i 0) (rep_vec j (i + 1)) game,
    NE := extract_string_game (rev_range i 0) (range j m) game,
    E := extract_string_game (rep_vec i (m + 1)) (range j m) game,
    SE := extract_string_game (range i n) (range j m) game,
    S := extract_string_game (range i n) (rep_vec j (n - i + 1)) game,
    SW := extract_string_game (range i n) (rev_range j 0) game,
    W := extract_string_game (rep_vec i (j + 1)) (rev_range j 0) game,
    NW := extract_string_game (rev_range i 0) (rev_range j 0) game
  }


def rev_string (s : String) := 
  s.toList |>.reverse |>.asString

def parse_xxmas (field : Field) (game : Game) : Nat := 
  let i := field.i
  let j := field.j
  let n := game.n
  let m := game.m
  if (1 ≤ i &&  i < (n - 1)) && (1 ≤ j && j < m -1) then
    -- south east
    let se := 
      extract_string_game (range (i - 1) (i + 2)) (range (j - 1) (j + 2)) game
    -- north east
    let ne := 
      extract_string_game (range (i - 1) (i + 2)) (rev_range (j + 1) (j - 1)) game
    if (se == "MAS" || (rev_string se) == "MAS") 
      && (ne == "MAS" || (rev_string ne) == "MAS") then
      1
    else 
      0
  else 
    0


def check_order (s : String) : Bool :=
  let rec helper (chars : List Char) (target : List Char) (used : List Char) : Bool :=
    match target with
    | [] => true  
    | t :: ts =>
      match chars with
      | [] => false
      | c :: cs => 
        -- not entirely clear what "even overlapping other words" means
        -- - we drop leading X and search for MAS
        -- - we cannot use the same character twice
        -- - we cannot use other target characters when searching for current
        --   - XAMASAAA; we cannot use A when searching for M, thus XMAS not in
        --     this.
        if c == 'X' || used.contains c || ts.contains c then
          false
        else if c == t then 
          helper cs ts (used.insert t) 
        else 
          helper cs target used       
  helper s.toList ['M', 'A', 'S'] []

def check_directions (directions : Directions) : Nat :=
  [directions.N, directions.NE, directions.E, directions.SE, 
   directions.S, directions.SW, directions.W, directions.NW] 
    |>.map check_order 
    |>.map (fun b => if b then 1 else 0)
    |>.foldl (· + ·) 0


def build_simple (config : Config) (fs : List (List Field)) := 
  let n := config.n
  let m := config.m
  let indices := mat_indices n m |> List.join
  build_mat fs {n := n, m := m} >>= 
  fun game => 
  let fields := game.fields
  let ou := (
    fun (i, j) => 
      get_field fields i j >>= 
      fun field =>
        match field.c with
        | 'X' => 
          some (parse_routes field game |> check_directions)
        | _ => none
    ) <$> indices
  pure ou


def reshape (n m : Nat) (mat : List α) := 
  let rs := List.zip (List.replicate n 0) (List.range (m + 1))
    |>.map (fun (i, j) => i + j * m)
  List.zip rs (rs.drop 1) |>.map (fun (i, j) => (mat.take j |>.drop i))


def sum_fields (l : List (Option (Field × Nat))) := 
  l.reduceOption |>.map (fun (_, x) => 
    x
  ) |>.foldl (· + ·) 0

def eval (s : String) (config : Config) := 
  let game :=  (parse_game s).run config
  match game with
  | Except.error e => 
    IO.println s!"Error: {e}"
  | Except.ok g => 
    let indices := mat_indices g.n g.m |> List.join
    let ou := (
      fun (i, j) => 
        get_field g.fields i j >>= 
        fun field =>
          match field.c with
          | 'X' => 
            some (field, parse_routes field g |> check_directions)
          | _ => none
      ) <$> indices 
      let final_sum := ou |> sum_fields
      IO.println s!"Solution 1: {final_sum}"

def eval2 (s : String) (config : Config) := 
  let game :=  (parse_game s).run config
  match game with
  | Except.error e => 
    IO.println s!"Error: {e}"
  | Except.ok g => 
    let indices := mat_indices g.n g.m |> List.join
    let ou := (
      fun (i, j) => 
        get_field g.fields i j >>= 
        fun field =>
          match field.c with
          | 'A' => 
            some (parse_xxmas field g)
          | _ => none
      ) <$> indices 
      let final_sum := ou.reduceOption |>.foldl (· + ·) 0
      IO.println s!"Solution 2: {final_sum}"
  

def main : IO Unit := do
  let config := {n := 140, m := 140 : Config}
  let grid_str ← read_string
  eval grid_str config
  eval2 grid_str config

/- tests -/
/- def teststr := "MMMSXXMASM -/
/- MSAMXMSMSA -/
/- AMXSXMAAMM -/
/- MSAMASMSMX -/
/- XMASAMXAMM -/
/- XXAMMXXAMA -/
/- SMSMSASXSS -/
/- SAXAMASAAA -/
/- MAMMMXMMMM -/
/- MXMXAXMASX" -/

/- #eval eval teststr {n := 10, m := 10 : Config} -/
/- #eval eval2 teststr {n := 10, m := 10 : Config} -/
