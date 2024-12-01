day1:
    mkdir -p day1
    aocd 1 > day1/input.txt
    lean --run day1/main.lean < day1/input.txt
