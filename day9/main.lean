import Aoc.Utils

inductive ObjectType where
| File
| Space
deriving Repr, BEq

structure DiskObject where
  type : ObjectType
  id : String
  num : Nat
  idx: Nat
deriving Repr, BEq

instance : ToString DiskObject where
  toString x := match x.type with
  | .File => s!"DiskObject(type=file, id={x.id}, num={x.num}, idx={x.idx})"
  | .Space => s!"DiskObject(type=space, id={x.id}, num={x.num}, idx={x.idx})"

def char_to_nat (c : Char) := 
  -- hacky
  c.toNat - '0'.toNat

def parse_disk_map_helper
  (map : List Char) (counter : Nat) (acc_idx : Nat) (soFar : List DiskObject) := 
  match map with
  | [] => soFar
  | c :: cs => 
    let num := char_to_nat c
    if counter % 2 == 0 then
      let id := toString (counter / 2) 
      let obj : DiskObject := ⟨ObjectType.File, id, num, acc_idx⟩
      parse_disk_map_helper cs (counter + 1) (acc_idx + num) (soFar ++ [obj])
    else
      let id := "-1"
      let obj : DiskObject := ⟨ObjectType.Space, id, num, acc_idx⟩
      parse_disk_map_helper cs (counter + 1) (acc_idx + num) (soFar ++ [obj])

def parse_disk_map (map : List Char) :=
  parse_disk_map_helper map 0 0 []

def object_to_str (o : DiskObject) := 
  match o.type with
  | .Space => List.replicate o.num "."
  | .File =>List.replicate o.num o.id

def parse_objects (objects : List DiskObject) := 
  objects.map (λo => object_to_str o) |>.join |>.toArray

def Fin.next? (fin : Fin n) : Option (Fin n) := 
  if h : fin.val + 1 < n then
    some (⟨fin.val + 1, h⟩)
  else
    none

def Fin.find? (i : Nat) (upper: Nat) : Option (Fin upper) :=
  if h : i < upper then
    some (⟨i, h⟩)
  else
    none

theorem decrementing_idx (arr : Array String) (n : Nat) (h : n < arr.size)
  : arr.size - (n + 1) < arr.size - n := by
  have h1 : arr.size - n ≠ 0 := by
    have h01 := Nat.sub_pos_of_lt h
    have h02 :=  Nat.ne_of_gt h01
    assumption
  rw [←Nat.sub_sub]
  have h2 := Nat.sub_one_lt h1
  apply h2

def find_right (rev_arr : Array String) : Option (Nat × Nat)  :=
  let val :=  rev_arr.findIdx? (λc => c ≠ ".")
  let as := rev_arr.size - 1
  match val with
  | some idx => some (as - idx, idx)
  | none => none

def move_files_helper (arr rev_arr : Array String) (i_l_c : Nat) :=
  -- hacky?
  if h : i_l_c < arr.size then
    let i_l : Fin arr.size := ⟨i_l_c, h⟩
    let i_r := find_right rev_arr
    match i_r with
    | some (i_r, i_r_rev) => 
      if i_l_c > i_r then  -- indices has passed each other
        arr
      else if hy : i_r < arr.size then
        let i_r : Fin arr.size := ⟨i_r, hy⟩
        let val := arr.get i_l
        have hfin := decrementing_idx arr i_l_c h
        if val == "." then
          move_files_helper (arr.swap i_l i_r) (rev_arr.set! i_r_rev val) (i_l_c + 1)
        else
          -- Case: found val wasn't "."; continue to next char in string
          move_files_helper arr rev_arr (i_l_c + 1)
      else
        arr
      | _ => arr
  else 
    arr
termination_by arr.size - i_l_c

def move_files (arr : Array String) := 
  move_files_helper arr arr.reverse 0

def checksum (arr : Array String) := 
  let idx := (List.range arr.size) |>.toArray
  idx.zip arr |>.map (
    λ(i, a) => match a.toNat? with
    | some x => i * x
    | none => 0
  )

def pop_last (arr : Array α) : Option (Array α × α) :=
  match arr.back? with
  | none   => none
  | some v => some (arr.pop, v)


def find_idx (as : Array α) (p : α → Bool) : Option (Fin as.size) := 
  match as.findIdx? p with
  | some idx => 
    if h : idx < as.size then
      some ⟨idx, h⟩
    else 
      none
  | none => none

theorem same_size_insert (arr : Array α) (i : Fin arr.size) (val : α) :
  (arr.set i val).size = arr.size := by
    have h0 := Array.size_set arr i val
    apply h0

def update_fin_set_array (arr : Array α) (i j: Fin arr.size) (val : α) := 
  have hx : j < (arr.set i val).size := by
    rw [Array.size_set arr i val]
    apply j.isLt
  have f_u : Fin (arr.set i val).size := ⟨j, by assumption⟩
  f_u

def update_equal (arr : Array DiskObject) (space file : DiskObject) 
  (idx f_idx : Fin arr.size) 
  := 
  let xobj := {space with idx := file.idx}
  let fobj := {file with idx := space.idx}
  let arr_1 := arr.set idx fobj
  arr_1.set (update_fin_set_array arr idx f_idx fobj) xobj


def update_split (arr : Array DiskObject) (space file : DiskObject) 
  (idx f_idx : Fin arr.size) := 
  let num_extra_space := space.num - file.num
  -- replace swapped with space
  let nobj : DiskObject := ⟨ObjectType.Space, "-1", file.num, file.idx⟩
  let arr_1 := arr.set f_idx nobj  
  -- insert swapped object + extra space
  let fobj := {file with idx := space.idx : DiskObject}
  -- insert file object at first part of swapped space
  let idx_1 := update_fin_set_array arr f_idx idx nobj
  let arr_2 := arr_1.set idx_1 fobj 
  -- prove valid index extra space; insert into arr_2
  let eobj : DiskObject 
    := ⟨ObjectType.Space, "-1", num_extra_space, space.idx + file.num⟩
  arr_2.insertAt! (idx_1 + 1) eobj -- insert extra space; too lazy to prove

def move_file_blocks_helper (arr : Array DiskObject) (files : List DiskObject) := 
  match files with
  | [] => arr
  | f :: fs => 
    let x_find := find_idx arr (λo => o.num ≥ f.num && o.type == ObjectType.Space)
    let f_find := find_idx arr (λo => o.id == f.id)
    match x_find, f_find with
    | some idx, some f_idx => 
      let x := arr.get idx
      let file := arr.get f_idx
      if idx > f_idx then
        -- space is after file; invalid; continue
        move_file_blocks_helper arr fs
      else 
        if x.num == f.num then
          let arr := update_equal arr x file idx f_idx
          move_file_blocks_helper arr fs
        else -- x.num > f.num
          let arr := update_split arr x file idx f_idx
          move_file_blocks_helper arr fs
    | _, _ => 
        move_file_blocks_helper arr fs

def move_file_blocks (arr : List DiskObject) := 
  -- start from last file
  let files := arr.filter (λo => o.type == ObjectType.File) |>.reverse 
  move_file_blocks_helper arr.toArray files


def main : IO Unit := do
  let s ← read_file "day9/input.txt"
  let parsed := parse_disk_map s.toList
  let arr := parsed |> parse_objects
  IO.println s!"Length: {arr.size}"
  let output := move_files arr |> checksum |>.foldl (· + ·) 0
  IO.println s!"Solution 1: {output}"
  let output2 := parsed |> move_file_blocks 
    |>.toList 
    |> parse_objects 
    |> checksum |>.foldl (· + ·) 0
  IO.println s!"Solution 2: {output2}"

-- tests

def teststr1 := "12345"
def teststr2 := "2333133121414131402"

def o1 := "022111222......"
def o2 := "0099811188827773336446555566.............."

def test : IO Unit := do
  let arr := parse_disk_map teststr1.toList |> parse_objects
  let a1 := move_files arr |>.toList |> String.intercalate ""
  let c1 := a1 == o1
  let arr := parse_disk_map teststr2.toList |> parse_objects
  let a2 := move_files arr
  let a2_1 := a2 |>.toList |> String.intercalate ""
  let c2 := a2_1 == o2
  let c3 := (a2 |> checksum |>.foldl (· + ·) 0) == 1928
  IO.println s!"{[c1, c2, c3].all (·)}"

/- #eval test -/

-- Tests solution 2

/- #eval parse_disk_map teststr2.toList -/ 
/- #eval parse_disk_map teststr2.toList |> move_file_blocks -/
/- #eval parse_disk_map teststr2.toList |> move_file_blocks -/
/- #eval (  -- missing last .; first part totally wrong :thinking: -/
/-   parse_disk_map teststr2.toList |> move_file_blocks -/ 
/-   |>.toList |> parse_objects |>.toList |> String.intercalate "" -/
/- ) -/
/- #eval (  -- missing last .; first part totally wrong :thinking: -/
/-   parse_disk_map teststr2.toList |> move_file_blocks -/ 
/-   |>.toList |> parse_objects |> checksum |>.foldl (· + ·) 0 -/
/- ) -/


def t_list : Array DiskObject := #[
 { type := ObjectType.File, id := "0", num := 2, idx := 0 },
 { type := ObjectType.Space, id := "-1", num := 3, idx := 2 },
 { type := ObjectType.File, id := "1", num := 3, idx := 5 },
 { type := ObjectType.Space, id := "-1", num := 3, idx := 8 },
 { type := ObjectType.File, id := "2", num := 1, idx := 11 },
 { type := ObjectType.Space, id := "-1", num := 3, idx := 12 },
 { type := ObjectType.File, id := "3", num := 3, idx := 15 },
 { type := ObjectType.Space, id := "-1", num := 1, idx := 18 },
 { type := ObjectType.File, id := "4", num := 1, idx := 19 }
 ]

def space : DiskObject := { type := ObjectType.Space, id := "-1", num := 3, idx := 2 }
def file : DiskObject := { type := ObjectType.File, id := "3", num := 3, idx := 15 }

-- test 2
def space1 : DiskObject := { type := ObjectType.Space, id := "-1", num := 3, idx := 2 }
def file1 : DiskObject := { type := ObjectType.File, id := "4", num := 1, idx := 19 }

/- #eval update_equal t_list space file ⟨1,  by decide⟩ ⟨6,  by decide⟩ -/
/- #eval update_split t_list space1 file1 ⟨1,  by decide⟩ ⟨8,  by decide⟩ -/
