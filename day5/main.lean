import Aoc.Utils
import Std

structure Order where
  fst : Nat
  snd : Nat
deriving Repr

structure Data where
  rules : List Order
  pages : List (List Nat)
deriving Repr


def parse_data (lines : List String) : Data := 
  {
    rules := 
      lines.filter (λ x => x.contains '|') 
        |>.map (λx => x.splitOn "|")
        |>.map (λx => x.map (λx => x.toNat!))
        |>.map (λx => {fst := x.get! 0, snd := x.get! 1 :Order})
    pages := 
      lines.filter (λ x => !x.contains '|' && !x.isEmpty) 
        |>.map (λx => x.splitOn ",")
        |>.map (λx => x.map (λx => x.toNat!))
  }


def extract_pairs (data : Data) := 
  let bools := data.pages.map (
    λx => data.rules.map (
      λr => 
        if x.contains r.fst && x.contains r.snd then
          -- how to evaluate inequality?
          if x.indexOf r.fst < x.indexOf r.snd then
            some true
          else 
            some false
        else
          none
    ) 
    |>.reduceOption
  )
  -- returns list of bools to index pages
  let filters := bools.map (λl => l.all (λb => b)) 
  List.zip data.pages filters 


def extract_valid (data : Data) := 
  let pairs := extract_pairs data
  pairs |>.filter (λ(_, b) => b) 
    |>.map (λ(l, _) => l)

def extract_invalid (data : Data) := 
  let pairs := extract_pairs data
  pairs |>.filter (λ(_, b) => !b) 
    |>.map (λ(l, _) => l)

def count_middle (pages : List (List Nat))  := 
  pages.map (
    λl => 
      let idx := (l.length / 2 + 1 - 1)
      l.get! idx
  ) 
    |>.foldl (· + ·) 0

def fix_printer (data : Data) := 
  let valid := extract_valid data
  valid |> count_middle


def build_dep_map (pairs : List Order) : Std.HashMap Nat (List Nat) :=
  pairs.foldl (fun map pair =>
    let deps := map.getD pair.fst []
    map.insert pair.fst (pair.snd :: deps)
  ) Std.HashMap.empty

def compare (dep_map : Std.HashMap Nat (List Nat)) (x y : Nat) : Ordering :=
  if dep_map.getD x [] |>.contains y then Ordering.lt
  else if dep_map.getD y [] |>.contains x then Ordering.gt
  else Ordering.eq


def fix_printer_2 (data : Data) := 
  let invalid := extract_invalid data
  let dep_map := build_dep_map data.rules
  let sorted := invalid.map (
    λl => l.toArray.qsort (fun a b => compare dep_map a b == Ordering.lt)
  )
  sorted.map (λa => a.toList) |> count_middle


def main : IO Unit := do
  let input ← read_string
  let sol := parse_data (input.splitOn "\n") |> fix_printer
  IO.println s!"Solution 1: {sol}"

  let sol2 := parse_data (input.splitOn "\n") |> fix_printer_2
  IO.println s!"Solution 2: {sol2}"


-- tests
/- def teststr := "47|53 -/
/- 97|13 -/
/- 97|61 -/
/- 97|47 -/
/- 75|29 -/
/- 61|13 -/
/- 75|53 -/
/- 29|13 -/
/- 97|29 -/
/- 53|29 -/
/- 61|53 -/
/- 97|53 -/
/- 61|29 -/
/- 47|13 -/
/- 75|47 -/
/- 97|75 -/
/- 47|61 -/
/- 75|61 -/
/- 47|29 -/
/- 75|13 -/
/- 53|13 -/

/- 75,47,61,53,29 -/
/- 97,61,53,29,13 -/
/- 75,29,13 -/
/- 75,97,47,61,53 -/
/- 61,13,29 -/
/- 97,13,75,29,47" -/
/- #eval parse_data (teststr.splitOn "\n") -/
/- #eval parse_data (teststr.splitOn "\n") |> extract_valid -/
/- #eval parse_data (teststr.splitOn "\n") |> extract_invalid -/
/- #eval parse_data (teststr.splitOn "\n") |> fix_printer -/ 
/- #eval parse_data (teststr.splitOn "\n") |> fix_printer_2 -/
