def read_lines : IO (Array String) := do
  let stdin ← IO.getStdin
  let mut lines : Array String := #[]
  while true do
    let line ← stdin.getLine
    if line.isEmpty then
      break
    lines := lines.push line.trimRight
  return lines

def read_string : IO String := do
  let stdin ← IO.getStdin
  let mut lines : List String := []
  while true do 
    let line ← stdin.getLine
    if line.isEmpty then
      break
    lines := lines.insert line
  return lines.foldl (· ++ ·) ""


def read_lines_lists (converter : String → α) : IO (Array (List α)) := do
  let stdin ← IO.getStdin
  let mut lines : Array (List α) := #[]
  while true do
    let line ← stdin.getLine
    if line.isEmpty then
      break
    lines := lines.push (line.trimRight.splitOn " " |>.map converter)
  return lines
