def read_lines : IO (Array String) := do
  let stdin ← IO.getStdin
  let mut lines : Array String := #[]
  while true do
    let line ← stdin.getLine
    if line.isEmpty then
      break
    lines := lines.push line.trimRight
  return lines

def main : IO Unit := do
  let lines ← read_lines
  let proc_lines := (
    lines.map (·.splitOn "   ") 
    |>.map (fun l => (l[0]!, l[1]!))
    |>.map (fun (a, b) => (a.toInt!, b.toInt!))
    )
  let first := proc_lines.map (fun pair => pair.fst) |>.qsort (· < ·)
  let second := proc_lines.map (fun pair => pair.snd) |>.qsort (· < ·)
  let pairs := Array.zip first second 
  let total_distance := pairs
    |>.map (fun (a, b) => (b - a).natAbs)
    |>.foldl (· + ·) 0
  IO.println s!"Solution 1: {total_distance}"
  let filtered := first.map (
    fun x => x * (second.filter (· == x) |>.size |> Int.ofNat)
  ) |>.foldl (· + ·) 0
  IO.println s!"Solution 2: {filtered}"
