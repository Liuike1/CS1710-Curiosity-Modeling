#lang forge/froglet

abstract sig Boolean {}
one sig True, False extends Boolean {}

abstract sig Piece {}
abstract sig T, I, L, J, S, Z extends Piece {}

one sig O extends Piece {}
one sig T_1, T_2, T_3, T_4 extends T {}
one sig I_v, I_h extends I {}
one sig L_1, L_2, L_3, L_4 extends L {}
one sig J_1, J_2, J_3, J_4 extends J {}
one sig S_d, S_u extends S {}
one sig Z_d, Z_u extends Z {}

sig State {
  board: pfunc Int -> Int -> Boolean,
  nexts: lone State,
  nextp: lone Piece
}

fun mirror[col: Int]: Int {
    subtract[3, col]
}

// Shape 1 Start

pred isShape1[s: State]{
    all x, y: Int | {
        (0 <= x and x <= 3 and 0 <= y and y <= 2) implies {
            some s.board[x][y]
            s.board[x][y] = True iff (y = 0 and (x = 0 or x = 1 or x = 2))
        }
        (not (0 <= x and x <= 3 and 0 <= y and y <= 2)) implies {
            no s.board[x][y]
        }
    }
}

pred isShape1Mirror[s: State]{
    all x, y: Int | {
        (0 <= x and x <= 3 and 0 <= y and y <= 2) implies {
            some s.board[x][y]
            s.board[x][y] = True iff (y = 0 and (x = 3 or x = 2 or x = 1))
        }
        (not (0 <= x and x <= 3 and 0 <= y and y <= 2)) implies {
            no s.board[x][y]
        }
    }
}
// Shape 1 End

// Shape 2 Start
pred isShape2[s: State]{
    all x, y: Int | {
        (0 <= x and x <= 3 and 0 <= y and y <= 2) implies {
            some s.board[x][y]
            s.board[x][y] = True iff (x = 0 and (y = 0 or y = 1 or y = 2))
        }
        (not (0 <= x and x <= 3 and 0 <= y and y <= 2)) implies {
            no s.board[x][y]
        }
    }
}

pred isShape2Mirror[s: State]{
    all x, y: Int | {
        (0 <= x and x <= 3 and 0 <= y and y <= 2) implies {
            some s.board[x][y]
            s.board[x][y] = True iff (x = 3 and (y = 0 or y = 1 or y = 2))
        }
        (not (0 <= x and x <= 3 and 0 <= y and y <= 2)) implies {
            no s.board[x][y]
        }
    }
}
// Shape 2 End

// Shape 3 Start
pred isShape3[s: State]{
    all x, y: Int | {
        (0 <= x and x <= 3 and 0 <= y and y <= 2) implies {
            some s.board[x][y]
            s.board[x][y] = True iff ((x = 0 and y = 0) or (x = 1 and y = 0) or (x = 3 and y = 0))
        }
        (not (0 <= x and x <= 3 and 0 <= y and y <= 2)) implies {
            no s.board[x][y]
        }
    }
}

pred isShape3Mirror[s: State]{
    all x, y: Int | {
        (0 <= x and x <= 3 and 0 <= y and y <= 2) implies {
            some s.board[x][y]
            s.board[x][y] = True iff ((x = 3 and y = 0) or (x = 2 and y = 0) or (x = 0 and y = 0))
        }
        (not (0 <= x and x <= 3 and 0 <= y and y <= 2)) implies {
            no s.board[x][y]
        }
    }
}
// Shape 3 End

// Shape 4 Start
pred isShape4[s: State]{
    all x, y: Int | {
        (0 <= x and x <= 3 and 0 <= y and y <= 2) implies {
            some s.board[x][y]
            s.board[x][y] = True iff ((x = 0 and y = 0) or (x = 1 and y = 1) or (x = 3 and y = 0))
        }
        (not (0 <= x and x <= 3 and 0 <= y and y <= 2)) implies {
            no s.board[x][y]
        }
    }
}

pred isShape4Mirror[s: State]{
    all x, y: Int | {
        (0 <= x and x <= 3 and 0 <= y and y <= 2) implies {
            some s.board[x][y]
            s.board[x][y] = True iff ((x = 3 and y = 0) or (x = 2 and y = 1) or (x = 0 and y = 0))
        }
        (not (0 <= x and x <= 3 and 0 <= y and y <= 2)) implies {
            no s.board[x][y]
        }
    }
}
// Shape 4 End

// Shape 5 Start
pred isShape5[s: State]{
    all x, y: Int | {
        (0 <= x and x <= 3 and 0 <= y and y <= 2) implies {
            some s.board[x][y]
            s.board[x][y] = True iff ((x = 0 and y = 0) or (x = 0 and y = 1) or (x = 1 and y = 0))
        }
        (not (0 <= x and x <= 3 and 0 <= y and y <= 2)) implies {
            no s.board[x][y]
        }
    }
}

pred isShape5Mirror[s: State]{
    all x, y: Int | {
        (0 <= x and x <= 3 and 0 <= y and y <= 2) implies {
            some s.board[x][y]
            s.board[x][y] = True iff ((x = 3 and y = 0) or (x = 3 and y = 1) or (x = 2 and y = 0))
        }
        (not (0 <= x and x <= 3 and 0 <= y and y <= 2)) implies {
            no s.board[x][y]
        }
    }
}
// Shape 5 End

// Shape 6 Start
pred isShape6[s: State]{
    all x, y: Int | {
        (0 <= x and x <= 3 and 0 <= y and y <= 2) implies {
            some s.board[x][y]
            s.board[x][y] = True iff ((x = 1 and y = 1) or (x = 0 and y = 1) or (x = 1 and y = 0))
        }
        (not (0 <= x and x <= 3 and 0 <= y and y <= 2)) implies {
            no s.board[x][y]
        }
    }
}

pred isShape6Mirror[s: State]{
    all x, y: Int | {
        (0 <= x and x <= 3 and 0 <= y and y <= 2) implies {
            some s.board[x][y]
            s.board[x][y] = True iff ((x = 2 and y = 1) or (x = 3 and y = 1) or (x = 2 and y = 0))
        }
        (not (0 <= x and x <= 3 and 0 <= y and y <= 2)) implies {
            no s.board[x][y]
        }
    }
}
// Shape 6 End

// Shape 7 Start
pred isShape7[s: State]{
    all x, y: Int | {
        (0 <= x and x <= 3 and 0 <= y and y <= 2) implies {
            some s.board[x][y]
            s.board[x][y] = True iff ((x = 0 and y = 0) or (x = 0 and y = 1) or (x = 2 and y = 0))
        }
        (not (0 <= x and x <= 3 and 0 <= y and y <= 2)) implies {
            no s.board[x][y]
        }
    }
}

pred isShape7Mirror[s: State]{
    all x, y: Int | {
        (0 <= x and x <= 3 and 0 <= y and y <= 2) implies {
            some s.board[x][y]
            s.board[x][y] = True iff ((x = 3 and y = 0) or (x = 3 and y = 1) or (x = 1 and y = 0))
        }
        (not (0 <= x and x <= 3 and 0 <= y and y <= 2)) implies {
            no s.board[x][y]
        }
    }
}
// Shape 7 End

// Shape 8 Start
pred isShape8[s: State]{
    all x, y: Int | {
        (0 <= x and x <= 3 and 0 <= y and y <= 2) implies {
            some s.board[x][y]
            s.board[x][y] = True iff ((x = 0 and y = 0) or (x = 1 and y = 0) or (x = 1 and y = 3))
        }
        (not (0 <= x and x <= 3 and 0 <= y and y <= 2)) implies {
            no s.board[x][y]
        }
    }
}

pred isShape8Mirror[s: State]{
    all x, y: Int | {
        (0 <= x and x <= 3 and 0 <= y and y <= 2) implies {
            some s.board[x][y]
            s.board[x][y] = True iff ((x = 3 and y = 0) or (x = 2 and y = 0) or (x = 2 and y = 3))
        }
        (not (0 <= x and x <= 3 and 0 <= y and y <= 2)) implies {
            no s.board[x][y]
        }
    }
}
// Shape 8 End

// Shape 9 Start
pred isShape9[s: State]{
    all x, y: Int | {
        (0 <= x and x <= 3 and 0 <= y and y <= 2) implies {
            some s.board[x][y]
            s.board[x][y] = True iff ((x = 0 and y = 0) or (x = 0 and y = 1) or (x = 1 and y = 1))
        }
        (not (0 <= x and x <= 3 and 0 <= y and y <= 2)) implies {
            no s.board[x][y]
        }
    }
}

pred isShape9Mirror[s: State]{
    all x, y: Int | {
        (0 <= x and x <= 3 and 0 <= y and y <= 2) implies {
            some s.board[x][y]
            s.board[x][y] = True iff ((x = 3 and y = 0) or (x = 3 and y = 1) or (x = 2 and y = 1))
        }
        (not (0 <= x and x <= 3 and 0 <= y and y <= 2)) implies {
            no s.board[x][y]
        }
    }
}
// Shape 9 End

// Shape 10 Start
pred isShape10[s: State]{
    all x, y: Int | {
        (0 <= x and x <= 3 and 0 <= y and y <= 2) implies {
            some s.board[x][y]
            s.board[x][y] = True iff ((x = 0 and y = 0) or (x = 1 and y = 0) or (x = 1 and y = 1))
        }
        (not (0 <= x and x <= 3 and 0 <= y and y <= 2)) implies {
            no s.board[x][y]
        }
    }
}

pred isShape10Mirror[s: State]{
    all x, y: Int | {
        (0 <= x and x <= 3 and 0 <= y and y <= 2) implies {
            some s.board[x][y]
            s.board[x][y] = True iff ((x = 3 and y = 0) or (x = 2 and y = 0) or (x = 2 and y = 1))
        }
        (not (0 <= x and x <= 3 and 0 <= y and y <= 2)) implies {
            no s.board[x][y]
        }
    }
}
// Shape 10 End

// Shape 11 Start
pred isShape11[s: State]{
    all x, y: Int | {
        (0 <= x and x <= 3 and 0 <= y and y <= 2) implies {
            some s.board[x][y]
            s.board[x][y] = True iff ((x = 0 and y = 0) or (x = 0 and y = 1) or (x = 3 and y = 0))
        }
        (not (0 <= x and x <= 3 and 0 <= y and y <= 2)) implies {
            no s.board[x][y]
        }
    }
}

pred isShape11Mirror[s: State]{
    all x, y: Int | {
        (0 <= x and x <= 3 and 0 <= y and y <= 2) implies {
            some s.board[x][y]
            s.board[x][y] = True iff ((x = 3 and y = 0) or (x = 3 and y = 1) or (x = 0 and y = 0))
        }
        (not (0 <= x and x <= 3 and 0 <= y and y <= 2)) implies {
            no s.board[x][y]
        }
    }
}
// Shape 11 End

// Shape 12 Start
pred isShape12[s: State]{
    all x, y: Int | {
        (0 <= x and x <= 3 and 0 <= y and y <= 2) implies {
            some s.board[x][y]
            s.board[x][y] = True iff ((x = 1 and y = 0) or (x = 2 and y = 0) or (x = 3 and y = 1))
        }
        (not (0 <= x and x <= 3 and 0 <= y and y <= 2)) implies {
            no s.board[x][y]
        }
    }
}

pred isShape12Mirror[s: State]{
    all x, y: Int | {
        (0 <= x and x <= 3 and 0 <= y and y <= 2) implies {
            some s.board[x][y]
            s.board[x][y] = True iff ((x = 2 and y = 0) or (x = 1 and y = 0) or (x = 0 and y = 1))
        }
        (not (0 <= x and x <= 3 and 0 <= y and y <= 2)) implies {
            no s.board[x][y]
        }
    }
}
// Shape 12 End

// Shape 13 Start
pred isShape13[s: State]{
    all x, y: Int | {
        (0 <= x and x <= 3 and 0 <= y and y <= 2) implies {
            some s.board[x][y]
            s.board[x][y] = True iff ((x = 0 and y = 0) or (x = 2 and y = 0) or (x = 3 and y = 1))
        }
        (not (0 <= x and x <= 3 and 0 <= y and y <= 2)) implies {
            no s.board[x][y]
        }
    }
}

pred isShape13Mirror[s: State]{
    all x, y: Int | {
        (0 <= x and x <= 3 and 0 <= y and y <= 2) implies {
            some s.board[x][y]
            s.board[x][y] = True iff ((x = 3 and y = 0) or (x = 1 and y = 0) or (x = 0 and y = 1))
        }
        (not (0 <= x and x <= 3 and 0 <= y and y <= 2)) implies {
            no s.board[x][y]
        }
    }
}
// Shape 13 End

// Shape 14 Start
pred isShape14[s: State]{
    all x, y: Int | {
        (0 <= x and x <= 3 and 0 <= y and y <= 2) implies {
            some s.board[x][y]
            s.board[x][y] = True iff ((x = 0 and y = 0) or (x = 1 and y = 1) or (x = 2 and y = 1))
        }
        (not (0 <= x and x <= 3 and 0 <= y and y <= 2)) implies {
            no s.board[x][y]
        }
    }
}

pred isShape14Mirror[s: State]{
    all x, y: Int | {
        (0 <= x and x <= 3 and 0 <= y and y <= 2) implies {
            some s.board[x][y]
            s.board[x][y] = True iff ((x = 3 and y = 0) or (x = 2 and y = 1) or (x = 1 and y = 1))
        }
        (not (0 <= x and x <= 3 and 0 <= y and y <= 2)) implies {
            no s.board[x][y]
        }
    }
}
// Shape 14 End


pred o_hole[x, y: Int, s: State] {
  s.nextp = O
  s.board[x,y] = False
  s.board[add[x,1],y] = False
  s.board[x,add[y,1]] = False
  s.board[add[x,1],add[y,1]] = False
}

pred i_vert_hole[x: Int, s: State] {
  s.nextp = I_v
  s.board[x,0] = False
  s.board[x,1] = False
  s.board[x,2] = False
}

pred i_horz_hole[y: Int, s: State] {
  s.nextp = I_h
  s.board[0,y] = False
  s.board[1,y] = False
  s.board[2,y] = False
  s.board[3,y] = False
}

pred s_down_hole[x, y: Int, s: State] {
  s.nextp = S_d
  s.board[x,y] = False
  s.board[add[x,1],y] = False
  s.board[add[x,1],add[y,1]] = False
  s.board[add[x,2],add[y,1]] = False
}

pred s_up_hole[x, y: Int, s: State] {
  s.nextp = S_u
  s.board[x,y] = False
  s.board[x,add[y,1]] = False
  s.board[subtract[x,1],add[y,1]] = False
  s.board[subtract[x,1],add[y,2]] = False
}

pred z_down_hole[x, y: Int, s: State] {
  s.nextp = Z_d
  s.board[x,y] = False
  s.board[add[x,1],y] = False
  s.board[add[x,1],subtract[y,1]] = False
  s.board[add[x,2],subtract[y,1]] = False
}

pred z_up_hole[x, y: Int, s: State] {
  s.nextp = Z_u
  s.board[x,y] = False
  s.board[x,add[y,1]] = False
  s.board[add[x,1],add[y,1]] = False
  s.board[add[x,1],add[y,2]] = False
}

pred l1_hole[x, y: Int, s: State] {
  s.nextp = L_1
  s.board[x,y] = False
  s.board[add[x,1],y] = False
  s.board[add[x,2],y] = False
  s.board[add[x,2],add[y,1]] = False
}

pred l2_hole[x, y: Int, s: State] {
  s.nextp = L_2
  s.board[x,y] = False
  s.board[add[x,1],y] = False
  s.board[x,add[y,1]] = False
  s.board[x,add[y,2]] = False
}

pred l3_hole[x, y: Int, s: State] {
  s.nextp = L_3
  s.board[x,y] = False
  s.board[x,add[y,1]] = False
  s.board[add[x,1],add[y,1]] = False
  s.board[add[x,2],add[y,1]] = False
}

pred l4_hole[x, y: Int, s: State] {
  s.nextp = L_4
  s.board[x,y] = False
  s.board[x,add[y,1]] = False
  s.board[x,add[y,2]] = False
  s.board[subtract[x,1],add[y,2]] = False
}

pred j1_hole[x, y: Int, s: State] {
  s.nextp = J_1
  s.board[x,y] = False
  s.board[x,add[y,1]] = False
  s.board[add[x,1],y] = False
  s.board[add[x,2],y] = False
}

pred j2_hole[x, y: Int, s: State] {
  s.nextp = J_2
  s.board[x,y] = False
  s.board[x,add[y,1]] = False
  s.board[x,add[y,2]] = False
  s.board[add[x,1],add[y,2]] = False
}

pred j3_hole[x, y: Int, s: State] {
  s.nextp = J_3
  s.board[x,y] = False
  s.board[add[x,1],y] = False
  s.board[add[x,2],y] = False
  s.board[add[x,2],subtract[y,1]] = False
}

pred j4_hole[x, y: Int, s: State] {
  s.nextp = J_4
  s.board[x,y] = False
  s.board[add[x,1],y]
  s.board[add[x,1],add[y,1]] = False
  s.board[add[x,1],add[y,2]] = False
}

pred t1_hole[x, y: Int, s: State] {
  s.nextp = T_1
  s.board[x,y] = False
  s.board[add[x,1],y] = False
  s.board[add[x,2],y] = False
  s.board[add[x,1],add[y,1]] = False
}

pred t2_hole[x, y: Int, s: State] {
  s.nextp = T_2
  s.board[x,y] = False
  s.board[x,add[y,1]] = False
  s.board[add[x,1],add[y,1]] = False
  s.board[x,add[y,2]] = False
}

pred t3_hole[x, y: Int, s: State] {
  s.nextp = T_3
  s.board[x,y] = False
  s.board[x,add[y,1]] = False
  s.board[add[x,1],add[y,1]] = False
  s.board[subtract[x,1],add[y,1]] = False
}

pred t4_hole[x, y: Int, s: State] {
  s.nextp = T_4
  s.board[x,y] = False
  s.board[x,add[y,1]] = False
  s.board[subtract[x,1],add[y,1]] = False
  s.board[x,add[y,2]] = False
}



pred line_clear[x,y: Int, s: State] {
    s.board[0,y] = True
    s.board[1,y] = True
    s.board[2,y] = True
    s.board[3,y] = True
}

test1: run {some s1, s2: State | {
        s1 != s2
        isShape14[s1]
        isShape14Mirror[s2]
    }} for exactly 2 State