import Std
import Aoc.Utils
import Aoc.Matrix

structure Robot where
  pos : Int × Int
  vel : Int × Int
deriving Repr

def parse_robots (s : String) : List (Option Robot) := 
  s.splitOn "\n" 
    -- anything to avoid slow regex lib :)
    |>.map (λs => s.splitOn " ")
    |>.map (
      λl => l.map (
        λs => 
          match s.splitOn "=" with
          | [_, v] =>  -- `_` robot type
            let ints := v.splitOn ","
            let x := ints.head!.toInt!
            let y := ints.getLast!.toInt!
            some (x, y)
          | _ => none
      ))
    |>.map (
      λl => 
        let p := l.head!
        let v := l.getLast!
        match p, v with
        | some (px, py), some (vx, vy) => 
          -- note: Positive x means the robot is moving to the right, and
          -- positive y means the robot is moving down; corresponds to (i, j)
          -- in 2d matrix; flip coords.
          some ⟨(py, px), (vy, vx)⟩
        | _, _ => none
    )

structure RobotGame where
  n : Nat
  m : Nat
deriving Repr

instance : ToString Robot := 
  ⟨λr => s!"pos: {r.pos}, vel: {r.vel}"⟩


def simulate (robot : Robot) : ReaderM RobotGame Robot := do
  let (x, y) := robot.pos
  let (vx, vy) := robot.vel
  let nx := x + vx
  let ny := y + vy
  let n := (←read).n
  let m := (←read).m
  /-
  - inside
  - out top, inside
  - inside, out left
  - out down, inside
  - inside, out right
  - out top, out left
  - out down, out right
  - out down, out left
  - out top, out tight
  -/
  if (nx ≥ 0 && nx < n) && (ny ≥ 0 && ny < m) then
    pure {robot with pos := (nx, ny)}
  else if nx < 0 && (ny ≥ 0 && ny < m) then
    let nx := n + nx
    pure {robot with pos := (nx, ny)}
  else if (nx ≥ 0 && nx < n) && ny < 0 then
    let ny := m + ny
    pure {robot with pos := (nx, ny)}
  else if nx ≥ n && (ny ≥ 0 && ny < m) then
    let nx := nx - n
    pure {robot with pos := (nx, ny)}
  else if (nx ≥ 0 && nx < n) && ny ≥ m then
    let ny := ny - m
    pure {robot with pos := (nx, ny)}
  else if nx < 0 && ny < 0 then
    let nx := n + nx
    let ny := m + ny
    pure {robot with pos := (nx, ny)}
  else if nx ≥ n && ny ≥ m then
    let nx := nx - n
    let ny := ny - m
    pure {robot with pos := (nx, ny)}
  else if nx ≥ n && ny < 0 then
    let nx := nx - n
    let ny := m + ny
    pure {robot with pos := (nx, ny)}
  else if nx < 0 && ny ≥ m then
    let nx := n + nx
    let ny := ny - m
    pure {robot with pos := (nx, ny)}
  else
    pure robot

def simulate_many (robot : Robot) (num : Nat) : ReaderM RobotGame Robot := do
  let mut r := robot
  for _ in [0:num] do -- non-inclusive
    r ← simulate r 
  pure r

def simulate_all (robots : List Robot) (num : Nat) 
  : ReaderM RobotGame (List Robot) := do
 robots.mapM (λr => simulate_many r num)

def robot := {pos := (4, 2), vel := (-3, 2) : Robot}

def simulate_several : IO Unit := do
  let r :=  Id.run (simulate robot |>.run {n :=  7, m := 11})
  let r1 :=  Id.run (simulate r |>.run {n :=  7, m := 11})
  let r2 :=  Id.run (simulate r1 |>.run {n :=  7, m := 11})
  IO.println s!"{r}; {r1}; {r2}"

def List.singleton {α : Type} (a : α) : List α :=
  [a]

def List.flatMap (a : List α) (b : α → List β) : List β := 
  join (map b a)

instance : Applicative List where
  pure := List.singleton
  seq f x := List.flatMap f fun y => Functor.map y (x ())

def simulate_robot (r : Option Robot) (num : Nat) := 
  match r with
  | some r => 
    some (simulate_many r num)
  | none => none

def count_robots (robots : List Robot) := 
 let map : Std.HashMap (Int × Int) Nat := Std.HashMap.empty
 robots.foldl (
   λacc r => 
   let val := acc.getD r.pos 0 + 1
   acc.insert r.pos val
 ) map

def count_valid (map : Std.HashMap (Int × Int) Nat) (n m : Nat) := 
  let strip_hori := n / 2  -- 0-indexed; e.g. 7 / 2 = 3 (4th middle row)
  let strip_vert := m / 2 
  let keys := map.keys |>.filter (
    λ (x, y) => 
      if x == strip_hori || y == strip_vert then
        false
      else
        true
  )
  map.filter (λk _ => keys.contains k)

def myMap : Std.HashMap (Int × Int) Nat :=
  Std.HashMap.ofList [((1, 2), 10), ((3, 3), 20), ((3, 5), 30)]

instance : BEq (Int × Int) where
  beq x y := x.fst == y.fst && x.snd == y.snd

instance : ToString (Std.HashMap (Int × Int) Nat) := 
  ⟨λm => 
    let pairs := m.toList.map (λ(k, v) => s!"{k} -> {v}")
    s!"Map({pairs})"
  ⟩
instance : ToString (Std.HashMap Nat Nat) := 
  ⟨λm => 
    let pairs := m.toList.map (λ(k, v) => s!"{k} -> {v}")
    s!"Map({pairs})"
  ⟩


def increment_map (map : Std.HashMap Nat Nat) (k v: Nat) := 
  let val := map.getD k 0
  map.insert k (val + v)

def count_quadrants (map : Std.HashMap (Int × Int) Nat) (n m : Nat)
  : Std.HashMap Nat Nat := 
  let sh := n / 2
  let sv := m / 2 
  map.keys.foldl (
    λacc pos => 
      let (x, y) := pos
      let val := map.getD pos 0
      if x < sh && y < sv then
        increment_map acc 0 val
      else if x < sh && y > sv then
        increment_map acc 1 val
      else if x > sh && y < sv then
        increment_map acc 2 val
      else if x > sh && y > sv then
        increment_map acc 3 val
      else
        acc
  ) Std.HashMap.empty


def plot_fields (extra : List Field) (n m : Nat) : IO Unit := do
  let ranges : List Field := cartesian_pairs (range_fin n) (range_fin m)
    |>.map (λ(f1, f2) => ⟨f1.val, f2.val, '.'⟩)
  let rs := reshape n m ranges
  let g := build_mat rs |>.run {n := n, m := m}
  match g with 
  | Except.error e => 
    IO.println s!"Error: {e}"
  | Except.ok game =>
    let game := extra.foldl (
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


def plot_final_state (valid : Std.HashMap (Int × Int) Nat) (n m : Nat) : IO Unit := 
 let fields : List Field := valid.keys.map (
  λk => 
    let val := valid.getD k 0
    let c := Char.ofNat (val + 48)
    ⟨k.fst.toNat, k.snd.toNat, c⟩
  )
 plot_fields fields n m

def get_mat_final_state (valid : Std.HashMap (Int × Int) Nat) (n m : Nat) 
  : Matrix n m Nat :=
 let extra := valid.keys.map (
  λk => 
    let val := valid.getD k 0
    (k.fst.toNat, k.snd.toNat, val)
  )
  let mat := construct_mat n m
  let mat := extra.foldl (
    λmat (i, j, val) => 
      if hi : i < n then
        if hj : j < m then
            mat.update_value ⟨i, hi⟩ ⟨j, hj⟩ val
        else
        mat
      else
      mat
  ) mat
  mat



def simulate_game 
  (s : String) (num : Nat) (n m : Nat) (plot : Bool := false) : IO Unit := do
 let robots := parse_robots s |>.reduceOption
 let robots := Id.run (simulate_all robots num |>.run {n := n, m := m})
 let map := count_robots robots
 let valid := count_valid map n m
 let quadrant := count_quadrants valid n m
 let res := quadrant.values.foldl (· * ·) 1
 if plot then 
  plot_final_state map n m else 
   IO.println s!"{res}"


def simulate_game_mat
  (s : String) (num : Nat) (n m : Nat) :=
 let robots := parse_robots s |>.reduceOption
 let robots := Id.run (simulate_all robots num |>.run {n := n, m := m})
 let map := count_robots robots
 let valid := count_valid map n m
 let quadrant := count_quadrants valid n m
 let res := quadrant.values.foldl (· * ·) 1
 let mat := get_mat_final_state valid n m
 let meas := emp_measure mat
 meas


def main (args : List String) : IO Unit := do
  let file ← read_file "day14/input.txt"
  match args with
  | ["1"] => simulate_game file 100 103 101  -- wide x tall
  | ["2", "plot", iter] => 
    for i in [0:iter.toNat!] do
      IO.println s!"Simulating iteration {i}"
      simulate_game file i 103 101 true
  | ["2", "sim", iter] => 
    let iter := iter.toNat!
    let mut l := []
    for i_fin in range_fin iter do
      let i := i_fin.val
      let x := simulate_game_mat file i 103 101
      IO.println s!"Simulating iteration {i}/{iter}"
      IO.println s!"{x}"
      if i % 1000 == 0 then IO.println s!"Unqs: {l.eraseDups}"
      l := l.append [x]
    IO.println s!"{l}"
  | ["2", "single", num] => 
    simulate_game file num.toNat! 103 101 true
  | _ => IO.println "Invalid arguments"

-- Tests

/- def test_str := "p=0,4 v=3,-3 -/
/- p=6,3 v=-1,-3 -/
/- p=10,3 v=-1,2 -/
/- p=2,0 v=2,-1 -/
/- p=0,0 v=1,3 -/
/- p=3,0 v=-2,-2 -/
/- p=7,6 v=-1,-3 -/
/- p=3,0 v=-1,-2 -/
/- p=9,3 v=2,3 -/
/- p=7,3 v=-1,2 -/
/- p=2,4 v=2,-3 -/
/- p=9,5 v=-3,-3" -/


/- #eval parse_robots test_str -/
/- #eval simulate robot |>.run {n :=  7, m := 11} -/

/- #eval simulate_many robot 4 |>.run {n :=  7, m := 11} -/
/- #eval simulate_many robot 5 |>.run {n :=  7, m := 11} -/
/- #eval simulate_several -/


/- #eval simulate_game test_str 100 7 11 -/
/- #check Game -/

