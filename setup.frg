#lang forge

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

// Shape 1 Start
pred isShape1[s: State] {
    all x, y: Int | s.board[x][y] = True iff (y = 0 and (x = 0 or x = 1 or x = 2))
}

pred isShape1Mirror[s: State] {
    all x, y: Int | s.board[x][y] = True iff (y = 0 and (x = 3 or x = 2 or x = 1))
}
// Shape 1 End

// Shape 2 Start
pred isShape2[s: State] {
    all x, y: Int | s.board[x][y] = True iff (x = 0 and (y = 0 or y = 1 or y = 2))
}

pred isShape2Mirror[s: State]{
    all x, y: Int | s.board[x][y] = True iff (x = 3 and (y = 0 or y = 1 or y = 2))
}
// Shape 2 End

// Shape 3 Start
pred isShape3[s: State]{
    all x, y: Int | {
        s.board[x][y] = True iff ((x = 0 and y = 0) or (x = 1 and y = 0) or (x = 3 and y = 0))
    }
}

pred isShape3Mirror[s: State]{
    all x, y: Int | {
        s.board[x][y] = True iff ((x = 3 and y = 0) or (x = 2 and y = 0) or (x = 0 and y = 0))
    }
}
// Shape 3 End

// Shape 4 Start
pred isShape4[s: State]{
    all x, y: Int | {
        s.board[x][y] = True iff ((x = 0 and y = 0) or (x = 1 and y = 1) or (x = 3 and y = 0))
    }
}

pred isShape4Mirror[s: State]{
    all x, y: Int | {
        s.board[x][y] = True iff ((x = 3 and y = 0) or (x = 2 and y = 1) or (x = 0 and y = 0))
    }
}
// Shape 4 End

// Shape 5 Start
pred isShape5[s: State]{
    all x, y: Int | {
        s.board[x][y] = True iff ((x = 0 and y = 0) or (x = 0 and y = 1) or (x = 1 and y = 0))
    }
}

pred isShape5Mirror[s: State]{
    all x, y: Int | {
        s.board[x][y] = True iff ((x = 3 and y = 0) or (x = 3 and y = 1) or (x = 2 and y = 0))
    }
}
// Shape 5 End

// Shape 6 Start
pred isShape6[s: State]{
    all x, y: Int | {
        s.board[x][y] = True iff ((x = 1 and y = 1) or (x = 0 and y = 1) or (x = 1 and y = 0))
    }
}

pred isShape6Mirror[s: State]{
    all x, y: Int | {
        s.board[x][y] = True iff ((x = 2 and y = 1) or (x = 3 and y = 1) or (x = 2 and y = 0))
    }
}
// Shape 6 End

// Shape 7 Start
pred isShape7[s: State]{
    all x, y: Int | {
        s.board[x][y] = True iff ((x = 0 and y = 0) or (x = 0 and y = 1) or (x = 2 and y = 0))
    }
}

pred isShape7Mirror[s: State]{
    all x, y: Int | {
        s.board[x][y] = True iff ((x = 3 and y = 0) or (x = 3 and y = 1) or (x = 1 and y = 0))
    }
}
// Shape 7 End

// Shape 8 Start
pred isShape8[s: State]{
    all x, y: Int | {
        s.board[x][y] = True iff ((x = 0 and y = 0) or (x = 1 and y = 0) or (x = 1 and y = 3))
    }
}

pred isShape8Mirror[s: State]{
    all x, y: Int | {
        s.board[x][y] = True iff ((x = 3 and y = 0) or (x = 2 and y = 0) or (x = 2 and y = 3))
    }
}
// Shape 8 End

// Shape 9 Start
pred isShape9[s: State]{
    all x, y: Int | {
        s.board[x][y] = True iff ((x = 0 and y = 0) or (x = 0 and y = 1) or (x = 1 and y = 1))
    }
}

pred isShape9Mirror[s: State]{
    all x, y: Int | {
        s.board[x][y] = True iff ((x = 3 and y = 0) or (x = 3 and y = 1) or (x = 2 and y = 1))
    }
}
// Shape 9 End

// Shape 10 Start
pred isShape10[s: State]{
    all x, y: Int | {
        s.board[x][y] = True iff ((x = 0 and y = 0) or (x = 1 and y = 0) or (x = 1 and y = 1))
    }
}

pred isShape10Mirror[s: State]{
    all x, y: Int | {
        s.board[x][y] = True iff ((x = 3 and y = 0) or (x = 2 and y = 0) or (x = 2 and y = 1))
    }
}
// Shape 10 End

// Shape 11 Start
pred isShape11[s: State]{
    all x, y: Int | {
        s.board[x][y] = True iff ((x = 0 and y = 0) or (x = 0 and y = 1) or (x = 3 and y = 0))
    }
}

pred isShape11Mirror[s: State]{
    all x, y: Int | {
        s.board[x][y] = True iff ((x = 3 and y = 0) or (x = 3 and y = 1) or (x = 0 and y = 0))
    }
}
// Shape 11 End

// Shape 12 Start
pred isShape12[s: State]{
    all x, y: Int | {
        s.board[x][y] = True iff ((x = 1 and y = 0) or (x = 2 and y = 0) or (x = 3 and y = 1))
    }
}

pred isShape12Mirror[s: State]{
    all x, y: Int | {
        s.board[x][y] = True iff ((x = 2 and y = 0) or (x = 1 and y = 0) or (x = 0 and y = 1))
    }
}
// Shape 12 End

// Shape 13 Start
pred isShape13[s: State]{
    all x, y: Int | {
        s.board[x][y] = True iff ((x = 0 and y = 0) or (x = 2 and y = 0) or (x = 3 and y = 1))
    }
}

pred isShape13Mirror[s: State]{
    all x, y: Int | {
        s.board[x][y] = True iff ((x = 3 and y = 0) or (x = 1 and y = 0) or (x = 0 and y = 1))
    }
}
// Shape 13 End

// Shape 14 Start
pred isShape14[s: State]{
    all x, y: Int | {
        s.board[x][y] = True iff ((x = 0 and y = 0) or (x = 1 and y = 1) or (x = 2 and y = 1))
    }
}

pred isShape14Mirror[s: State]{
    all x, y: Int | {
        s.board[x][y] = True iff ((x = 3 and y = 0) or (x = 2 and y = 1) or (x = 1 and y = 1))
    }
}
// Shape 14 End

// empty space for O
pred o_hole[x, y: Int, s: State] {
  s.nextp = O
  s.board[x,y] = False
  s.board[add[x,1],y] = False
  s.board[x,add[y,1]] = False
  s.board[add[x,1],add[y,1]] = False
}

// empty space for vertical I
pred i_vert_hole[x: Int, s: State] {
  s.nextp = I_v
  s.board[x,0] = False
  s.board[x,1] = False
  s.board[x,2] = False
}

// empty space for horizontal I
pred i_horz_hole[y: Int, s: State] {
  s.nextp = I_h
  s.board[0,y] = False
  s.board[1,y] = False
  s.board[2,y] = False
  s.board[3,y] = False
}

// empty space for S down
pred s_down_hole[x, y: Int, s: State] {
  s.nextp = S_d
  s.board[x,y] = False
  s.board[add[x,1],y] = False
  s.board[add[x,1],add[y,1]] = False
  s.board[add[x,2],add[y,1]] = False
}

// empty space for S up
pred s_up_hole[x, y: Int, s: State] {
  s.nextp = S_u
  s.board[x,y] = False
  s.board[x,add[y,1]] = False
  s.board[subtract[x,1],add[y,1]] = False
  s.board[subtract[x,1],add[y,2]] = False
}

// empty space for Z down
pred z_down_hole[x, y: Int, s: State] {
  s.nextp = Z_d
  s.board[x,y] = False
  s.board[add[x,1],y] = False
  s.board[add[x,1],subtract[y,1]] = False
  s.board[add[x,2],subtract[y,1]] = False
}

// empty space for Z up
pred z_up_hole[x, y: Int, s: State] {
  s.nextp = Z_u
  s.board[x,y] = False
  s.board[x,add[y,1]] = False
  s.board[add[x,1],add[y,1]] = False
  s.board[add[x,1],add[y,2]] = False
}

// empty space for L_1
pred l1_hole[x, y: Int, s: State] {
  s.nextp = L_1
  s.board[x,y] = False
  s.board[add[x,1],y] = False
  s.board[add[x,2],y] = False
  s.board[add[x,2],add[y,1]] = False
}

// empty space for L_2
pred l2_hole[x, y: Int, s: State] {
  s.nextp = L_2
  s.board[x,y] = False
  s.board[add[x,1],y] = False
  s.board[x,add[y,1]] = False
  s.board[x,add[y,2]] = False
}

// empty space for L_3
pred l3_hole[x, y: Int, s: State] {
  s.nextp = L_3
  s.board[x,y] = False
  s.board[x,add[y,1]] = False
  s.board[add[x,1],add[y,1]] = False
  s.board[add[x,2],add[y,1]] = False
}

// empty space for L_4
pred l4_hole[x, y: Int, s: State] {
  s.nextp = L_4
  s.board[x,y] = False
  s.board[x,add[y,1]] = False
  s.board[x,add[y,2]] = False
  s.board[subtract[x,1],add[y,2]] = False
}

// empty space for J_1
pred j1_hole[x, y: Int, s: State] {
  s.nextp = J_1
  s.board[x,y] = False
  s.board[x,add[y,1]] = False
  s.board[add[x,1],y] = False
  s.board[add[x,2],y] = False
}

// empty space for J_2
pred j2_hole[x, y: Int, s: State] {
  s.nextp = J_2
  s.board[x,y] = False
  s.board[x,add[y,1]] = False
  s.board[x,add[y,2]] = False
  s.board[add[x,1],add[y,2]] = False
}

// empty space for J_3
pred j3_hole[x, y: Int, s: State] {
  s.nextp = J_3
  s.board[x,y] = False
  s.board[add[x,1],y] = False
  s.board[add[x,2],y] = False
  s.board[add[x,2],subtract[y,1]] = False
}

// empty space for J_4
pred j4_hole[x, y: Int, s: State] {
  s.nextp = J_4
  s.board[x,y] = False
  s.board[add[x,1],y]
  s.board[add[x,1],add[y,1]] = False
  s.board[add[x,1],add[y,2]] = False
}

// empty space for T_1
pred t1_hole[x, y: Int, s: State] {
  s.nextp = T_1
  s.board[x,y] = False
  s.board[add[x,1],y] = False
  s.board[add[x,2],y] = False
  s.board[add[x,1],add[y,1]] = False
}

// empty space for T_2
pred t2_hole[x, y: Int, s: State] {
  s.nextp = T_2
  s.board[x,y] = False
  s.board[x,add[y,1]] = False
  s.board[add[x,1],add[y,1]] = False
  s.board[x,add[y,2]] = False
}

// empty space for T_3
pred t3_hole[x, y: Int, s: State] {
  s.nextp = T_3
  s.board[x,y] = False
  s.board[x,add[y,1]] = False
  s.board[add[x,1],add[y,1]] = False
  s.board[subtract[x,1],add[y,1]] = False
}

// empty space for T_4
pred t4_hole[x, y: Int, s: State] {
  s.nextp = T_4
  s.board[x,y] = False
  s.board[x,add[y,1]] = False
  s.board[subtract[x,1],add[y,1]] = False
  s.board[x,add[y,2]] = False
}

// checking if there is a full line
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