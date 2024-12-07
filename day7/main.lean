import Aoc.Utils

def load (s: String)  := 
  let proc_lines := (
    s.splitOn "\n" 
    |>.filter (fun x => !x.isEmpty)
    |>.map (·.splitOn ":") 
    |>.map (fun l => (l[0]!, l[1]!))
    |>.map (
      fun (a, b) => (
        a.toNat!,
        b.trim |>.splitOn " " |>.map String.toNat!
      )
    )
  )
  proc_lines

def concat_nats (n1 n2 : Nat) : Nat := 
  s!"{n1}{n2}" |> String.toNat!

def base_fns := [Nat.add, Nat.mul]
def fns_ext := [Nat.add, Nat.mul, concat_nats]

def fn_combs (n : Nat) (base_fns : List (Nat → Nat → Nat)) := 
  let sets := List.range (n - 1) |>.map (λ_ => base_fns)  -- repeat
  let cartesian_product := 
    sets.foldl (fun acc s => 
      acc.bind (fun a => 
        s.bind (fun b => 
          [a ++ [b]]
        )
      )
    ) [[]]
  cartesian_product 

def fold_several (funcs : List (Nat → Nat → Nat)) (nums : List Nat) : Nat :=
  match nums, funcs with
  | [], _ => 0  -- No numbers to fold
  | x :: xs, _ => 
    -- [(f1, x1), (f2, x2), ..., (fn-1, xn-1)] with x0 init
    xs.zip funcs
      |>.foldl (fun acc (num, func) => func acc num) x 

def solve (s : String) (base_fns : List (Nat → Nat → Nat)) : Nat := 
  /- let s1 := [0, 1] -/
  let data := load s
  let all := data.map (
    λ(total, nums) => 
      let evals := fn_combs (nums.length) base_fns
      |>.map (λfns => fold_several fns nums)
      (total, evals)
  )
  let total_calibration_result := all.filter (
    λ(total, evals) => evals.contains (total)
  ) |>.foldl (λacc (total, _) => acc + total) 0
  total_calibration_result

def main : IO Unit := do
  let file ← read_file "day7/input.txt"
  let s1 := solve file base_fns
  IO.println s!"Solution 1: {s1}"
  let s2 := solve file fns_ext  -- slow but works :)
  IO.println s!"Solution 2: {s2}"

-- tests
/- def test2 : IO Unit := -/ 
/-   /1- let s1 := [0, 1] -1/ -/
/-   let nums := [11, 6, 16, 20] -/
/-   let all_fns := fn_combs (nums.length) base_fns -/
/-   let res := all_fns.map (λfns => fold_several fns nums) -/
/-   IO.println s!"{res}" -/
  
/- def teststr := "190: 10 19 -/
/- 3267: 81 40 27 -/
/- 83: 17 5 -/
/- 156: 15 6 -/
/- 7290: 6 8 6 15 -/
/- 161011: 16 10 13 -/
/- 192: 17 8 14 -/
/- 21037: 9 7 18 13 -/
/- 292: 11 6 16 20" -/

/- #eval solve teststr base_fns -/
/- #eval solve teststr fns_ext -/
/- #eval test2 -/
/- #eval concat_nats 20 30 -/
