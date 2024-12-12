def remove_duplicate_chars (s so_far: List Char) (last : Char) : List Char := 
  match s with
  | [] => so_far
  | h :: t => 
    if h == last then
      remove_duplicate_chars t so_far h
    else
      remove_duplicate_chars t (so_far ++ [h]) h

def rm_dup (s : String) : String := 
  let chars := s.toList
  remove_duplicate_chars chars [] ' ' |>.asString
