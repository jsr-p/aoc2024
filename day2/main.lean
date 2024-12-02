import Aoc.Utils

structure Report where
  numbers: List Nat
  diffs: List Int
  id: Nat 
deriving Repr

structure ValidatedReport where
  all_pos : Bool
  valid_range : Bool
deriving Repr

instance : ToString Report where
  toString r := s!"Numbers: {r.numbers}; -> Diffs: {r.diffs}"


def differences (lst : List Nat) : List Int :=
  List.zip lst lst.tail |>.map (fun (x, y) => y - x)

def is_valid_diff (x : Int) : Bool := 
  x.natAbs ≥ 1 && x.natAbs ≤ 3

def validate_report (x : Report) (is_valid_fn : Int → Bool) : ValidatedReport := 
  {
      -- all pos or all neg
      all_pos := x.diffs.all (· > 0) || x.diffs.all (· < 0),
      -- diffs in valid range
      valid_range := x.diffs.all is_valid_fn 
  }

def validate_reports (reports : Array Report) (is_valid_fn : Int → Bool) :
Array ValidatedReport := 
  reports.map (fun x => validate_report x is_valid_fn)

def is_valid_report (report : ValidatedReport) : Bool := 
  report.all_pos && report.valid_range

def count_valid (validated_reports : Array ValidatedReport) : Nat := 
  validated_reports.map (fun x => Bool.toNat (is_valid_report x))
    |>.foldl (· + ·) 0

def filter_value_invalid_report (x : Report) (is_valid_fn : Int → Bool) 
(add_idx : Nat := 1) : Report := 
  -- add 1 while diff is taken from second entry
  let invalid_idx := x.diffs.findIdx (fun x => is_valid_fn x) + add_idx
  -- take until invalid_idx, drop invalid, then takes rest after invalid
  let numbers := x.numbers.take invalid_idx ++ x.numbers.drop (invalid_idx + 1)
  {
    numbers := numbers,
    diffs := differences numbers,
    id := x.id
  }

def filter_invalid_reports (reports : Array Report) (is_valid_fn : Int → Bool)
: Array Report := 
  reports.filter (fun x => 
    (x.diffs.map (λ x => Bool.toNat (is_valid_fn x))  
    |>.foldl (· + ·) 0)
    == x.diffs.length - 1)

def check_case (diffs : List Int) (cond_all : List Int → Bool) (cond_single : Int →
Bool) := 
  let x :=  diffs.map (λ x => if cond_single x then 1 else 0) |>.foldl (· + ·) 0 |> (· == 1)
  let y := cond_all diffs
  x && y

structure FilteredReports where
  c1 : Array Report
  c2 : Array Report
  c3 : Array Report
  c4 : Array Report
  c5 : Array Report
  c6 : Array Report
deriving Repr

def sum_cond (lst : List Int) (cond : Int → Bool) := 
  lst.map (λ x => if cond x then 1 else 0) |>.foldl (· + ·) 0

def filter_reports (reps : Array Report) : FilteredReports := 
  {
    c1 := reps.filter (fun x => check_case x.diffs (fun x => x.all (· > 0)) (· > 3)),
    c2 := reps.filter (fun x => check_case x.diffs (fun x => x.all (· ≥ 0)) (· == 0)),
    c3 := reps.filter (fun x => check_case x.diffs (fun x => x.all (· ≤ 0)) (· == 0)),
    c4 := reps.filter (fun x => check_case x.diffs (fun x => x.all (· < 0)) (· < -3)),
    c5 := reps.filter (fun x => check_case x.diffs (
      fun x => sum_cond x (· < 0) == 1 && (sum_cond x (· > 0) == x.length - 1)
    ) (· < 0)),
    c6 := reps.filter (fun x => check_case x.diffs (
      fun x => sum_cond x (· > 0) == 1 && (sum_cond x (· < 0) == x.length - 1)
    ) (· > 0))
  }

def flatten_filtered (freps : FilteredReports) : Array Report := 
  freps.c1.map (fun x => filter_value_invalid_report x (· > 3))
  ++ freps.c1.map (fun x => filter_value_invalid_report x (· > 3) 0)
  ++ freps.c2.map (fun x => filter_value_invalid_report x (· == 0))
  ++ freps.c3.map (fun x => filter_value_invalid_report x (· == 0))
  ++ freps.c4.map (fun x => filter_value_invalid_report x (· < -3))
  ++ freps.c4.map (fun x => filter_value_invalid_report x (· < -3) 0)
  ++ freps.c5.map (fun x => filter_value_invalid_report x (· < 0) 0)
  ++ freps.c5.map (fun x => filter_value_invalid_report x (· < 0) 1)
  ++ freps.c6.map (fun x => filter_value_invalid_report x (· > 0) 0) 
  ++ freps.c6.map (fun x => filter_value_invalid_report x (· > 0) 1) 
  

def filter_valid (reps : Array Report) : Array Report := 
  reps.filter (fun x => validate_report x is_valid_diff |> is_valid_report)

def validate_filtered (filt_reps : Array Report) : Array ValidatedReport := 
  filt_reps |> (fun x => validate_reports x is_valid_diff)

def unique_ids (reps: Array Report) : Nat := 
  reps |>.map (fun x => x.id) |>.toList |>.eraseDups |>.length

def main : IO Unit := do
  let lines ← read_lines_lists String.toNat!
  -- 1
  let reports := lines.zip (Array.range lines.size) 
    |>.map (fun (x, i) => {numbers := x, diffs := differences x,  id := i: Report})
  let validated_reports := reports |> filter_valid
  let num_valid_reports := validated_reports |> unique_ids
  IO.print s!"Solution 1: {num_valid_reports}\n"

  -- 2 
  let ids := validated_reports.map (·.id)
  let other_reports := reports.filter (fun x => !ids.contains (x.id))
  let filtered := filter_reports other_reports |> flatten_filtered |> filter_valid 
  let count_extra := filtered |> unique_ids
  IO.println s!"{count_extra}"
  IO.println s!"Solution 2: {num_valid_reports + count_extra}"
