lean := "lake env lean"

all: day1 day2

day1:
    mkdir -p day1
    aocd 1 > day1/input.txt
    {{lean}} --run day1/main.lean < day1/input.txt

day2:
    mkdir -p day2
    aocd 2 > day2/input.txt
    {{lean}} --run day2/main.lean < day2/input.txt

day3:
    mkdir -p day3
    aocd 3 > day3/input.txt
    {{lean}} --run day3/main.lean < day3/input.txt
