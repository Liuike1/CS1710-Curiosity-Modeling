#lang forge/froglet

abstract sig Boolean {}
one sig True, False extends Boolean {}

// occupied takes [row],[col] and returns boolean
sig State {
    occupied: pfunc Int -> Int -> Boolean
}

fun mirror[col: Int]: Int {
    subtract[3, col]
}

// Shape 1 Start

pred isShape1[s: State]{
    all x, y: Int | {
        (0 <= x and x <= 3 and 0 <= y and y <= 2) implies {
            some s.occupied[x][y]
            s.occupied[x][y] = True iff (y = 0 and (x = 0 or x = 1 or x = 2))
        }
        (not (0 <= x and x <= 3 and 0 <= y and y <= 2)) implies {
            no s.occupied[x][y]
        }
    }
}

pred isShape1Mirror[s: State]{
    all x, y: Int | {
        (0 <= x and x <= 3 and 0 <= y and y <= 2) implies {
            some s.occupied[x][y]
            s.occupied[x][y] = True iff (y = 0 and (x = 3 or x = 2 or x = 1))
        }
        (not (0 <= x and x <= 3 and 0 <= y and y <= 2)) implies {
            no s.occupied[x][y]
        }
    }
}
// Shape 1 End

// Shape 2 Start
pred isShape2[s: State]{
    all x, y: Int | {
        (0 <= x and x <= 3 and 0 <= y and y <= 2) implies {
            some s.occupied[x][y]
            s.occupied[x][y] = True iff (x = 0 and (y = 0 or y = 1 or y = 2))
        }
        (not (0 <= x and x <= 3 and 0 <= y and y <= 2)) implies {
            no s.occupied[x][y]
        }
    }
}

pred isShape2Mirror[s: State]{
    all x, y: Int | {
        (0 <= x and x <= 3 and 0 <= y and y <= 2) implies {
            some s.occupied[x][y]
            s.occupied[x][y] = True iff (x = 3 and (y = 0 or y = 1 or y = 2))
        }
        (not (0 <= x and x <= 3 and 0 <= y and y <= 2)) implies {
            no s.occupied[x][y]
        }
    }
}
// Shape 2 End

// Shape 3 Start
pred isShape3[s: State]{
    all x, y: Int | {
        (0 <= x and x <= 3 and 0 <= y and y <= 2) implies {
            some s.occupied[x][y]
            s.occupied[x][y] = True iff ((x = 0 and y = 0) or (x = 1 and y = 0) or (x = 3 and y = 0))
        }
        (not (0 <= x and x <= 3 and 0 <= y and y <= 2)) implies {
            no s.occupied[x][y]
        }
    }
}

pred isShape3Mirror[s: State]{
    all x, y: Int | {
        (0 <= x and x <= 3 and 0 <= y and y <= 2) implies {
            some s.occupied[x][y]
            s.occupied[x][y] = True iff ((x = 3 and y = 0) or (x = 2 and y = 0) or (x = 0 and y = 0))
        }
        (not (0 <= x and x <= 3 and 0 <= y and y <= 2)) implies {
            no s.occupied[x][y]
        }
    }
}
// Shape 3 End

// Shape 4 Start
pred isShape4[s: State]{
    all x, y: Int | {
        (0 <= x and x <= 3 and 0 <= y and y <= 2) implies {
            some s.occupied[x][y]
            s.occupied[x][y] = True iff ((x = 0 and y = 0) or (x = 1 and y = 1) or (x = 3 and y = 0))
        }
        (not (0 <= x and x <= 3 and 0 <= y and y <= 2)) implies {
            no s.occupied[x][y]
        }
    }
}

pred isShape4Mirror[s: State]{
    all x, y: Int | {
        (0 <= x and x <= 3 and 0 <= y and y <= 2) implies {
            some s.occupied[x][y]
            s.occupied[x][y] = True iff ((x = 3 and y = 0) or (x = 2 and y = 1) or (x = 0 and y = 0))
        }
        (not (0 <= x and x <= 3 and 0 <= y and y <= 2)) implies {
            no s.occupied[x][y]
        }
    }
}
// Shape 4 End

// Shape 5 Start
pred isShape5[s: State]{
    all x, y: Int | {
        (0 <= x and x <= 3 and 0 <= y and y <= 2) implies {
            some s.occupied[x][y]
            s.occupied[x][y] = True iff ((x = 0 and y = 0) or (x = 0 and y = 1) or (x = 1 and y = 0))
        }
        (not (0 <= x and x <= 3 and 0 <= y and y <= 2)) implies {
            no s.occupied[x][y]
        }
    }
}

pred isShape5Mirror[s: State]{
    all x, y: Int | {
        (0 <= x and x <= 3 and 0 <= y and y <= 2) implies {
            some s.occupied[x][y]
            s.occupied[x][y] = True iff ((x = 3 and y = 0) or (x = 3 and y = 1) or (x = 2 and y = 0))
        }
        (not (0 <= x and x <= 3 and 0 <= y and y <= 2)) implies {
            no s.occupied[x][y]
        }
    }
}
// Shape 5 End

// Shape 6 Start
pred isShape6[s: State]{
    all x, y: Int | {
        (0 <= x and x <= 3 and 0 <= y and y <= 2) implies {
            some s.occupied[x][y]
            s.occupied[x][y] = True iff ((x = 1 and y = 1) or (x = 0 and y = 1) or (x = 1 and y = 0))
        }
        (not (0 <= x and x <= 3 and 0 <= y and y <= 2)) implies {
            no s.occupied[x][y]
        }
    }
}

pred isShape6Mirror[s: State]{
    all x, y: Int | {
        (0 <= x and x <= 3 and 0 <= y and y <= 2) implies {
            some s.occupied[x][y]
            s.occupied[x][y] = True iff ((x = 2 and y = 1) or (x = 3 and y = 1) or (x = 2 and y = 0))
        }
        (not (0 <= x and x <= 3 and 0 <= y and y <= 2)) implies {
            no s.occupied[x][y]
        }
    }
}
// Shape 6 End

// Shape 7 Start
pred isShape7[s: State]{
    all x, y: Int | {
        (0 <= x and x <= 3 and 0 <= y and y <= 2) implies {
            some s.occupied[x][y]
            s.occupied[x][y] = True iff ((x = 0 and y = 0) or (x = 0 and y = 1) or (x = 2 and y = 0))
        }
        (not (0 <= x and x <= 3 and 0 <= y and y <= 2)) implies {
            no s.occupied[x][y]
        }
    }
}

pred isShape7Mirror[s: State]{
    all x, y: Int | {
        (0 <= x and x <= 3 and 0 <= y and y <= 2) implies {
            some s.occupied[x][y]
            s.occupied[x][y] = True iff ((x = 3 and y = 0) or (x = 3 and y = 1) or (x = 1 and y = 0))
        }
        (not (0 <= x and x <= 3 and 0 <= y and y <= 2)) implies {
            no s.occupied[x][y]
        }
    }
}
// Shape 7 End

// Shape 8 Start
pred isShape8[s: State]{
    all x, y: Int | {
        (0 <= x and x <= 3 and 0 <= y and y <= 2) implies {
            some s.occupied[x][y]
            s.occupied[x][y] = True iff ((x = 0 and y = 0) or (x = 1 and y = 0) or (x = 1 and y = 3))
        }
        (not (0 <= x and x <= 3 and 0 <= y and y <= 2)) implies {
            no s.occupied[x][y]
        }
    }
}

pred isShape8Mirror[s: State]{
    all x, y: Int | {
        (0 <= x and x <= 3 and 0 <= y and y <= 2) implies {
            some s.occupied[x][y]
            s.occupied[x][y] = True iff ((x = 3 and y = 0) or (x = 2 and y = 0) or (x = 2 and y = 3))
        }
        (not (0 <= x and x <= 3 and 0 <= y and y <= 2)) implies {
            no s.occupied[x][y]
        }
    }
}
// Shape 8 End

// Shape 9 Start
pred isShape9[s: State]{
    all x, y: Int | {
        (0 <= x and x <= 3 and 0 <= y and y <= 2) implies {
            some s.occupied[x][y]
            s.occupied[x][y] = True iff ((x = 0 and y = 0) or (x = 0 and y = 1) or (x = 1 and y = 1))
        }
        (not (0 <= x and x <= 3 and 0 <= y and y <= 2)) implies {
            no s.occupied[x][y]
        }
    }
}

pred isShape9Mirror[s: State]{
    all x, y: Int | {
        (0 <= x and x <= 3 and 0 <= y and y <= 2) implies {
            some s.occupied[x][y]
            s.occupied[x][y] = True iff ((x = 3 and y = 0) or (x = 3 and y = 1) or (x = 2 and y = 1))
        }
        (not (0 <= x and x <= 3 and 0 <= y and y <= 2)) implies {
            no s.occupied[x][y]
        }
    }
}
// Shape 9 End

// Shape 10 Start
pred isShape10[s: State]{
    all x, y: Int | {
        (0 <= x and x <= 3 and 0 <= y and y <= 2) implies {
            some s.occupied[x][y]
            s.occupied[x][y] = True iff ((x = 0 and y = 0) or (x = 1 and y = 0) or (x = 1 and y = 1))
        }
        (not (0 <= x and x <= 3 and 0 <= y and y <= 2)) implies {
            no s.occupied[x][y]
        }
    }
}

pred isShape10Mirror[s: State]{
    all x, y: Int | {
        (0 <= x and x <= 3 and 0 <= y and y <= 2) implies {
            some s.occupied[x][y]
            s.occupied[x][y] = True iff ((x = 3 and y = 0) or (x = 2 and y = 0) or (x = 2 and y = 1))
        }
        (not (0 <= x and x <= 3 and 0 <= y and y <= 2)) implies {
            no s.occupied[x][y]
        }
    }
}
// Shape 10 End

// Shape 11 Start
pred isShape11[s: State]{
    all x, y: Int | {
        (0 <= x and x <= 3 and 0 <= y and y <= 2) implies {
            some s.occupied[x][y]
            s.occupied[x][y] = True iff ((x = 0 and y = 0) or (x = 0 and y = 1) or (x = 3 and y = 0))
        }
        (not (0 <= x and x <= 3 and 0 <= y and y <= 2)) implies {
            no s.occupied[x][y]
        }
    }
}

pred isShape11Mirror[s: State]{
    all x, y: Int | {
        (0 <= x and x <= 3 and 0 <= y and y <= 2) implies {
            some s.occupied[x][y]
            s.occupied[x][y] = True iff ((x = 3 and y = 0) or (x = 3 and y = 1) or (x = 0 and y = 0))
        }
        (not (0 <= x and x <= 3 and 0 <= y and y <= 2)) implies {
            no s.occupied[x][y]
        }
    }
}
// Shape 11 End

// Shape 12 Start
pred isShape12[s: State]{
    all x, y: Int | {
        (0 <= x and x <= 3 and 0 <= y and y <= 2) implies {
            some s.occupied[x][y]
            s.occupied[x][y] = True iff ((x = 1 and y = 0) or (x = 2 and y = 0) or (x = 3 and y = 1))
        }
        (not (0 <= x and x <= 3 and 0 <= y and y <= 2)) implies {
            no s.occupied[x][y]
        }
    }
}

pred isShape12Mirror[s: State]{
    all x, y: Int | {
        (0 <= x and x <= 3 and 0 <= y and y <= 2) implies {
            some s.occupied[x][y]
            s.occupied[x][y] = True iff ((x = 2 and y = 0) or (x = 1 and y = 0) or (x = 0 and y = 1))
        }
        (not (0 <= x and x <= 3 and 0 <= y and y <= 2)) implies {
            no s.occupied[x][y]
        }
    }
}
// Shape 12 End

// Shape 13 Start
pred isShape13[s: State]{
    all x, y: Int | {
        (0 <= x and x <= 3 and 0 <= y and y <= 2) implies {
            some s.occupied[x][y]
            s.occupied[x][y] = True iff ((x = 0 and y = 0) or (x = 2 and y = 0) or (x = 3 and y = 1))
        }
        (not (0 <= x and x <= 3 and 0 <= y and y <= 2)) implies {
            no s.occupied[x][y]
        }
    }
}

pred isShape13Mirror[s: State]{
    all x, y: Int | {
        (0 <= x and x <= 3 and 0 <= y and y <= 2) implies {
            some s.occupied[x][y]
            s.occupied[x][y] = True iff ((x = 3 and y = 0) or (x = 1 and y = 0) or (x = 0 and y = 1))
        }
        (not (0 <= x and x <= 3 and 0 <= y and y <= 2)) implies {
            no s.occupied[x][y]
        }
    }
}
// Shape 13 End

// Shape 14 Start
pred isShape14[s: State]{
    all x, y: Int | {
        (0 <= x and x <= 3 and 0 <= y and y <= 2) implies {
            some s.occupied[x][y]
            s.occupied[x][y] = True iff ((x = 0 and y = 0) or (x = 1 and y = 1) or (x = 2 and y = 1))
        }
        (not (0 <= x and x <= 3 and 0 <= y and y <= 2)) implies {
            no s.occupied[x][y]
        }
    }
}

pred isShape14Mirror[s: State]{
    all x, y: Int | {
        (0 <= x and x <= 3 and 0 <= y and y <= 2) implies {
            some s.occupied[x][y]
            s.occupied[x][y] = True iff ((x = 3 and y = 0) or (x = 2 and y = 1) or (x = 1 and y = 1))
        }
        (not (0 <= x and x <= 3 and 0 <= y and y <= 2)) implies {
            no s.occupied[x][y]
        }
    }
}
// Shape 14 End

test1: run {some s1, s2: State | {
        s1 != s2
        isShape14[s1]
        isShape14Mirror[s2]
    }} for exactly 2 State