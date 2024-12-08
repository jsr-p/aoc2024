import Aoc.Utils
import Aoc.Matrix

abbrev Point := Int × Int
abbrev DPoint := Int × Int

instance : Add Point where
  add := fun p1 p2 => (p1.1 + p2.1, p1.2 + p2.2)

instance : Sub Point where
  sub := fun p1 p2 => (p1.1 - p2.1, p1.2 - p2.2)

instance : HMul Int Point Point where
  hMul := fun x p1 => (x * p1.fst, x * p1.snd)
instance : HMul Nat Point Point where
  hMul := fun x p1 => (x * p1.fst, x * p1.snd)

structure AntiNodes where
  Δi : Int
  Δj : Int
  fst : Point
  snd : Point
deriving Repr

def antinodes (p1 p2 : Point) : AntiNodes := 
  let Δp := p2 - p1
  let Δi := Δp.fst
  let Δj := Δp.snd
  let σi := Δi.sign
  let σj := Δj.sign
  let aΔi := Δi.natAbs
  let aΔj := Δj.natAbs
  let a1 := p1 - (σi * aΔi, σj * aΔj)
  let a2 := p2 + (σi * aΔi, σj * aΔj)
  ⟨Δi, Δj, a1, a2⟩

def validate_antinode (a : Point) (n m : Nat) := 
  if 
    a.fst ≥ 0 && a.snd ≥ 0
    && a.fst < n && a.snd < m then
    true
  else 
    false

def nats_to_ints (l : List Nat) : List Int := 
  l.map (λx => Int.ofNat x)

def full_range (start stop : Int) : List Int :=
  if start > stop then
    []
  else if start < 0 && stop > 0 then
    let r1 := range 0 (start.natAbs + 1)  -- include negative lower bound
    let r2 := range 1 stop.natAbs
    let nums := (r1.map (λx => -Int.ofNat x ) |>.reverse) ++ (r2 |> nats_to_ints)
    nums
  else if start < 0 && stop ≤ 0 then  -- notice `≤` 
    -- include negative lower bound; exclude negative lower bound
    let r1 := range (stop.natAbs + 1) (start.natAbs + 1)
    r1.map (λx => -Int.ofNat x ) |>.reverse
  else
    range start.natAbs stop.natAbs |> nats_to_ints

def span_line_range (p2: Point) (saΔi saΔj : Int) (n m : Nat) : List Int :=
  -- Construct line based on p2 of the two points spanning line
  let ei0 := saΔi == 0
  let ej0 := saΔj == 0
  -- solve inequalities for constants:
  -- i₂ + k₁|Δi₂| > n
  -- j₂ + k₂|Δj₂| > m
  -- i₂ + k₃|Δi₂| < 0
  -- j₂ + k₄|Δj₂| < 0
  let kiu := (n - p2.snd) / saΔi + 2  -- ensure stricly greater/smaller with 2
  let kil := -p2.snd / saΔi - 2
  let kju := (m - p2.snd) / saΔj + 2 
  let kjl := -p2.snd / saΔj - 2
  match ei0, ej0 with
  | true, true => []
  | true, false => 
    -- same x coord
    full_range kjl kju
  | false, true => 
    -- same y coord
    full_range kil kiu
  | false, false => 
    -- take max for constants and construct range
    full_range (min kil kjl) (max kiu kju)

-- extended info
structure AntiNodesE where
  Δi : Int
  Δj : Int
  σi : Int
  σj : Int
  aΔi : Nat
  aΔj : Nat
deriving Repr

def anodes_info (p1 p2 : Point) : AntiNodesE := 
  let Δp := p2 - p1
  let Δi := Δp.fst
  let Δj := Δp.snd
  let σi := Δi.sign
  let σj := Δj.sign
  let aΔi := Δi.natAbs
  let aΔj := Δj.natAbs
  ⟨Δi, Δj, σi, σj, aΔi, aΔj⟩

def antinodes_line (p1 p2 : Point) (n m : Nat) : List Point :=
  let ai := anodes_info p1 p2
  let saΔi :=  ai.aΔi * ai.σi
  let saΔj :=  ai.aΔj * ai.σj
  let range := span_line_range p2 saΔi saΔj n m |>.drop 0  -- drop 0 if exists
  range.map (
    λk => p1 + k * (saΔi, saΔj)
  )
  
instance : Coe Field Point where
  coe x := (x.i, x.j)

def solve_1 (s : String) (n m : Nat) : IO Unit := do
  let game := parse_game s |>.run {n := n, m := m}
  match game with
  | Except.error e => 
    IO.println s!"Error: {e}"
  | Except.ok g => 
    let points := extract_fields g
      |>.filter (λf => f.c ≠ '.')
      |>.toList
    let pairs := points.bind (
      λp1 => points.map (
        λp2 => (p1, p2)
      )
    ) 
      |>.filter (λ(p1, p2) => p1.c == p2.c && !(equal_coords p1 p2))
    let antinodes := pairs.map (
      λ(p1, p2) => antinodes p1 p2
    )
      |>.bind (λa => [a.fst, a.snd])
      |>.filter (λp => validate_antinode p g.n g.m)
      |>.eraseDups
    let num_antinodes := antinodes |> List.length
    IO.println s!"Solution 1: {num_antinodes}"


def solve_2 (s : String) (n m : Nat) : IO Unit := do
  let game := parse_game s |>.run {n := n, m := m}
  match game with
  | Except.error e => 
    IO.println s!"Error: {e}"
  | Except.ok g => 
    let points := extract_fields g
      |>.filter (λf => f.c ≠ '.')
      |>.toList
    let pairs := points.bind (
      λp1 => points.map (
        λp2 => (p1, p2)
      )
    ) 
      |>.filter (λ(p1, p2) => p1.c == p2.c && !(equal_coords p1 p2))
    let antinodes := pairs.bind (
      λ(p1, p2) => antinodes_line p1 p2 n m
    )
      |>.filter (λp => validate_antinode p n m)
      |>.eraseDups
    let num_antinodes := antinodes |> List.length
    IO.println s!"Solution 2: {num_antinodes}"

def main : IO Unit := do
  let s ← read_file "day8/input.txt"
  solve_1 s 50 50
  solve_2 s 50 50



/- -- tests -/

/- def test_string := "............ -/
/- ........0... -/
/- .....0...... -/
/- .......0.... -/
/- ....0....... -/
/- ......A..... -/
/- ............ -/
/- ............ -/
/- ........A... -/
/- .........A.. -/
/- ............ -/
/- ............" -/


/- def test_line : IO Unit := do -/
/-   let p1 := (8, 8) -/
/-   let p2 := (9, 9) -/ 
/-   let ai := anodes_info p1 p2 -/
/-   let saΔi :=  ai.aΔi * ai.σi -/
/-   let saΔj :=  ai.aΔj * ai.σj -/
/-   let range := span_line_range p2 saΔi saΔj 12 12 -/
/-   let points := range.map ( -/
/-     λk => p1 + k * (saΔi, saΔj) -/
/-   ) -/
/-   IO.println s!"{range}" -/
/-   IO.println s!"{points}" -/

/- def test_lines : IO Unit := do -/
/-   let p1 := (8, 8) -/
/-   let p2 := (9, 9) -/ 
/-   let points := antinodes_line p1 p2 12 12 -/
/-   IO.println s!"{points}" -/

/-   let p1 := (4, 4) -/
/-   let p2 := (3, 7) -/ 
/-   let points := antinodes_line p1 p2 12 12 -/
/-   IO.println s!"{points}" -/
/-   let n := 12 -/ 
/-   let m := 12 -/
/-   let v := points |>.filter (λp => validate_antinode p n m) -/
/-   IO.println s!"{v}" -/


/- #eval solve_1 test_string 12 12 -/
/- #eval antinodes (5, 6) (9, 9) -/ 
/- #eval antinodes  (9, 9) (5, 6) -/
/- #eval solve_2 test_string 12 12  -- 852 is too low -/

/- #eval test_line -/
/- #eval test_lines -/

/- #eval full_range (3) (3) -/
/- #eval full_range (-3) 3 -/
/- #eval full_range (-3) 0 -/
/- #eval full_range (-3) 0 -/
/- #eval full_range 1 3 -/
