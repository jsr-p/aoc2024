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

day4:
    mkdir -p day4
    aocd 4 > day4/input.txt
    {{lean}} --run day4/main.lean < day4/input.txt

day5:
    mkdir -p day5
    aocd 5 > day5/input.txt
    {{lean}} --run day5/main.lean < day5/input.txt

day6:
    mkdir -p day6
    aocd 6 > day6/input.txt
    {{lean}} --run day6/main.lean < day6/input.txt
