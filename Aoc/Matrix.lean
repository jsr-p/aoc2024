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
      ) ""

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


def extract_fields (game : Game) := 
  -- Game starts facing up
  game.fields.val.map (fun row => row.val.map (·)) 
    |>.flatten

def equal_coords (f1 f2 : Field) : Bool := 
  f1.i == f2.i && f1.j == f2.j
