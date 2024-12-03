import Regex
import Regex.Syntax.Flavor
import Aoc.Utils


def eval_product (ele : Array (Option Regex.Match)) : Option Nat := 
  match ele with 
  | #[] => none
  | #[e1, e2] => 
    match e1, e2 with 
    | some e1, some e2 => 
      match e1.toNat?, e2.toNat? with
      | some e1, some e2 => some (e1 * e2)
      | _, _ => none
    | _, _ => none
  | _ => none

def sum_array (arr : Array (Option Nat)) : Nat :=
  arr.foldl (fun acc opt =>
    match opt with
    | some value => acc + value
    | none => acc
  ) 0


def build_rust_regex (s : String):= 
  Regex.build (flavor := Syntax.Flavor.Rust) s


structure Mult where
  val1 : Nat
  val2 : Nat
  start : Nat
deriving Repr

inductive Extra where
| do_op
| dont_op
| none_op
deriving Repr

structure ExtraInstructions where
  extra : Extra
  start : Nat
deriving Repr

def re := regex% r"mul\((\d+),(\d+)\)"
def re1 := regex% r"(don't\(\)|do\(\))" 

def get_mult_captures (s : String) := 
  let caps := Regex.all_captures s re
  caps.map (fun c => c.groups)

def sum_string (s : String) : Nat := 
  let eval := get_mult_captures s |>.map (fun c => eval_product c)
  sum_array eval


instance : ToString Extra where
  toString x := match x with
  | Extra.dont_op => "dont_op"
  | Extra.do_op => "do_op"
  | Extra.none_op => "none_op"

instance : ToString ExtraInstructions where
  toString x := s!"ExtraInstructions(extra={x.extra}, start={x.start})"

instance : ToString Mult where
  toString x := s!"Mult(val1={x.val1}, val2={x.val2}, start={x.start})"

instance : ToString (Mult × ExtraInstructions) where
  toString := fun (m, e) => s!"{m}; {e}"

def get_pairs (string : String) : Array (Mult × ExtraInstructions) := 
  let extra : Array ExtraInstructions := Regex.all_captures string re1 |>.map (
    fun c => 
      let groups := c.groups
      match groups with 
      | #[e1] => 
        match e1 with
          | some e1 => 
            let op := match e1.toString with
            | "don't()" => Extra.dont_op
            | "do()" => Extra.do_op
            | _ => Extra.none_op
            some (ExtraInstructions.mk op e1.startPos.byteIdx)
          | none => none
      | _ => none
    ) |>.filterMap (fun x => x)
  let s := get_mult_captures string |>.map (
    fun c => 
      let groups := c
      match groups with 
      | #[e1, e2] => 
        match e1, e2 with 
        | some e1, some e2 => 
          some (Mult.mk e1.toString.toNat! e2.toString.toNat! e1.startPos.byteIdx)
        | _, _ => none
      | _ => none
  ) |>.filterMap (fun x => x)
  let pairs : Array (Mult × ExtraInstructions) := s.map (fun mul => 
    match extra.filter (fun extra => mul.start > extra.start) with
      | #[] => Prod.mk mul (ExtraInstructions.mk Extra.none_op 0)
      | arr => 
          let diffs := arr.map (fun val => mul.start - val.start)
          match diffs |>.min? with 
            | some min_diff => 
                let idx := diffs.toList.findIdx (fun diff => diff == min_diff)
                match arr.get? idx with
                | some closest_extra => Prod.mk mul closest_extra
                | none => Prod.mk mul (ExtraInstructions.mk Extra.none_op 0)
            | none => 
              Prod.mk mul (ExtraInstructions.mk Extra.none_op 0)
    )
  pairs

def sum_string_2 (s : String) := 
  let pairs := get_pairs s 
  pairs |>.map (
    fun (m, e) => match e.extra with
    | Extra.none_op => m.val1 * m.val2
    | Extra.do_op => m.val1 * m.val2
    | Extra.dont_op => 0
    ) |>.foldl (· + ·) 0

def main : IO Unit := do
  let lines ← read_lines 

  -- 1:
  let sums := lines.map (fun s => sum_string s)
  IO.println s!"Solution 1: {sums |>.foldl Nat.add 0}"

  -- 2:
  let res2 := String.intercalate "" lines.toList |> sum_string_2
  IO.println s!"Solution 2: {res2}"

