import Regex
import Aoc.Utils
import Aoc.Matrix

def extract (mat : Matrix 2 2 Int) :=
  let a := mat.get_value 0 0
  let b := mat.get_value 0 1
  let c := mat.get_value 1 0
  let d := mat.get_value 1 1
  (a, b, c ,d)

def determinant (mat : Matrix 2 2 Int) := 
  let (a, b, c , d) := extract mat
  a * d - b * c

structure Inverse where
  x11 : Float
  x12 : Float
  x21 : Float
  x22 : Float
deriving Repr

def inverse (mat : Matrix 2 2 Int) : Inverse := 
  let (a, b, c, d) := extract mat
  let det := determinant mat
  let dinv : Float := 1 / (Float.ofInt det)
  let ai := dinv * (Float.ofInt a)
  let bi := -dinv * (Float.ofInt b)
  let ci := -dinv * (Float.ofInt c)
  let di := dinv * (Float.ofInt d)
  {x11 := di, x12 := bi, x21 := ci, x22 := ai : Inverse}

structure InverseComp where
  x11 : Int
  x12 : Int
  x21 : Int
  x22 : Int
  det : Int
deriving Repr

def solve (mat : Matrix 2 2 Int) (vec : Vec 2 Int) := 
  -- Solve Ax = b and check whether solution
  -- x = A^{-1}b is an integer solution
  let (a, b, c, d) := extract mat
  let det := determinant mat
  let (x, y) := (vec.gett 0, vec.gett 1)
  let y1 := d * x - b * y
  let y2 := -c * x + a * y
  let c1 := Int.tmod y1 det
  let c2 := Int.tmod y2 det
  /- dbg_trace s!"Conditions: {c1}; {c2}" -- Debug print -/
  match c1 == 0, c2 ==0 with
  | true, true => 
    some (y1 / det, y2 / det)
  | _, _ => none

def re_A := regex% r"Button A: X\+(\d+), Y\+(\d+)"
def re_B := regex% r"Button B: X\+(\d+), Y\+(\d+)"
def re2 := regex% r"Prize: X=(\d+), Y=(\d+)"

def get_capture (s : String) (regex : Regex) : 
  Option Regex.Match × Option Regex.Match := 
  match Regex.captures s regex with
  | some c => 
    match c.groups.get? 0, c.groups.get? 1 with
    | some c1, some c2 => (c1, c2)
    | _, _ => (none, none)
  | none => (none, none)


structure Machine where
  A : Int × Int
  B : Int × Int
  XY : Int × Int
deriving Repr

instance : ToString Machine where
  toString x := s!"Machine(A={x.A}, B={x.B}, XY={x.XY})"

def extract_pairs 
  (pair : Option Regex.Match × Option Regex.Match) : Option (Int × Int) := 
  match pair with
  | (some x, some y) => 
    match x.toNat?, y.toNat? with
    | some e1, some e2 => some (Int.ofNat e1, Int.ofNat e2)
    | _, _ => none
  | (_, _) => none

def parse_machine (gs : String) : Option Machine := do
  let A := get_capture gs re_A |> extract_pairs
  let B := get_capture gs re_B |> extract_pairs
  let XY := get_capture gs re2 |> extract_pairs
  match A, B, XY with
  | some A, some B, some XY => 
    some {A := A, B := B, XY := XY}
  | _, _, _ => none


def solve_machine (m : Machine) : Option (Int × Int) := 
  let (ax, ay) := m.A
  let (bx, b_y) := m.B
  let (x, y) := m.XY
  let mat : Matrix 2 2 Int := ⟨#[
    ⟨#[ax, bx], by simp⟩,
    ⟨#[ay, b_y], by simp⟩
  ], by simp⟩
  solve mat ⟨#[x, y], by simp⟩

def parse_data (s : String) := 
  let machines := s.splitOn "\n\n"
  machines |>.mapM (parse_machine)

def compute_price (pairs : List (Option (Int × Int))) := 
  let price := pairs.map (
    λo => match o with
    | some (x, y) => 3 * x + y
    | none => 0
  )
  price

def solve_1_2 (s : String) : IO Unit := do
  let ms := parse_data s
  match ms with
  | none => IO.println s!"Failed parsing machines"
  | some ms => 
    IO.println s!"Solving {ms.length} machines"
    let sol := ms.map (λm => solve_machine m)
    let price := compute_price sol
    IO.println s!"Part 1; Total tokens: {price |>.foldl (· + ·) 0}"

    -- part 2
    let fact := 10000000000000
    let mss := ms.map (λm => {m with XY := (m.XY.1 + fact, m.XY.2 + fact)})
    let sol := mss.map (λm => solve_machine m)
    let price := compute_price sol
    IO.println s!"Part 2; Total tokens: {price |>.foldl (· + ·) 0}"

def main : IO Unit := do
  let file ← read_file "day13/input.txt"
  solve_1_2 file

-- Tests


/- def teststr := "Button A: X+94, Y+34 -/
/- Button B: X+22, Y+67 -/
/- Prize: X=8400, Y=5400 -/

/- Button A: X+26, Y+66 -/
/- Button B: X+67, Y+21 -/
/- Prize: X=12748, Y=12176 -/

/- Button A: X+17, Y+86 -/
/- Button B: X+84, Y+37 -/
/- Prize: X=7870, Y=6450 -/

/- Button A: X+69, Y+23 -/
/- Button B: X+27, Y+71 -/
/- Prize: X=18641, Y=10279" -/

/- #eval parse_data teststr -/
/- #eval solve_1_2 teststr -/
/- def machine := {A := (94, 34), B := (22, 67), XY :=  (8400, 5400) : Machine} -/
/- #eval solve_machine machine -/
