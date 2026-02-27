#lang forge

open "setup.frg"

test suite for isShape1 {
  // Shape1 has exactly three cells filled
  threeCellsFilled: assert {
    all s: State | isShape1[s] implies {
      some x1, x2, x3, y1, y2, y3: Int | {
        x1 >= 0 and x1 <= 3 and y1 >= 0 and y1 <= 3
        x2 >= 0 and x2 <= 3 and y2 >= 0 and y2 <= 3
        x3 >= 0 and x3 <= 3 and y3 >= 0 and y3 <= 3
        (x1 -> y1) != (x2 -> y2)
        (x1 -> y1) != (x3 -> y3)
        (x2 -> y2) != (x3 -> y3)

        s.board[x1,y1] = True
        s.board[x2,y2] = True
        s.board[x3,y3] = True

        all p, q: Int | {
          p >= 0 and p <= 3 and q >= 0 and q <= 3
          (p -> q) != (x1 -> y1) and (p -> q) != (x2 -> y2) and (p -> q) != (x3 -> y3)
          } implies s.board[p,q] = False
      }
    }
  } is sat for exactly 1 State

  // the predicate actually has the correct shape
  example shape1Correct is {some s: State | isShape1[s]} for {
    Boolean = `True + `False
    True = `True
    False = `False
    Piece = `O + `T_1 + `T_2 + `T_3 + `T_4 + `L_1 + `L_2 + `L_3 + `L_4
      + `J_1 + `J_2 + `J_3 + `J_4 + `S_d + `S_u + `Z_d + `Z_u + `I_v + `I_h
    O = `O
    T_1 = `T_1
    T_2 = `T_2
    T_3 = `T_3
    T_4 = `T_4
    L_1 = `L_1
    L_2 = `L_2
    L_3 = `L_3
    L_4 = `L_4
    J_1 = `J_1
    J_2 = `J_2
    J_3 = `J_3
    J_4 = `J_4
    I_v = `I_v
    I_h = `I_h
    S_d = `S_d
    S_u = `S_u
    Z_d = `Z_d
    Z_u = `Z_u
    State = `S1
    board = `S1 -> (0 + 1 + 2) -> 0 -> `True + `S1 -> 3 -> 0 -> `False 
      + `S1 -> (0 + 1 + 2 + 3) -> (1 + 2 + 3) -> `False
  }
}

test suite for o_hole {
  // normal example using Shape5
  example s5_o_hole is {some s: State | o_hole[2,0,s]} for {
    Boolean = `True + `False
    True = `True
    False = `False
    Piece = `O + `T_1 + `T_2 + `T_3 + `T_4 + `L_1 + `L_2 + `L_3 + `L_4
      + `J_1 + `J_2 + `J_3 + `J_4 + `S_d + `S_u + `Z_d + `Z_u + `I_v + `I_h
    O = `O
    T_1 = `T_1
    T_2 = `T_2
    T_3 = `T_3
    T_4 = `T_4
    L_1 = `L_1
    L_2 = `L_2
    L_3 = `L_3
    L_4 = `L_4
    J_1 = `J_1
    J_2 = `J_2
    J_3 = `J_3
    J_4 = `J_4
    I_v = `I_v
    I_h = `I_h
    S_d = `S_d
    S_u = `S_u
    Z_d = `Z_d
    Z_u = `Z_u
    State = `S1
    board = `S1 -> 0 -> (0 + 1) -> `True + `S1 -> 1 -> 0 -> `True
      + `S1 -> 0 -> (2 + 3) -> `False + `S1 -> 1 -> (1 + 2 + 3) -> `False
      + `S1 -> (2 + 3) -> (0 + 1 + 2 + 3) -> `False
  }
}

test suite for next_piece_hole {
  // example hole for Z_d in Shape9
  example s9s14_Z_d_hole is {some s: State | next_piece_hole[2,1,s]} for {
    Boolean = `True + `False
    True = `True
    False = `False
    Piece = `O + `T_1 + `T_2 + `T_3 + `T_4 + `L_1 + `L_2 + `L_3 + `L_4
      + `J_1 + `J_2 + `J_3 + `J_4 + `S_d + `S_u + `Z_d + `Z_u + `I_v + `I_h
    O = `O
    T_1 = `T_1
    T_2 = `T_2
    T_3 = `T_3
    T_4 = `T_4
    L_1 = `L_1
    L_2 = `L_2
    L_3 = `L_3
    L_4 = `L_4
    J_1 = `J_1
    J_2 = `J_2
    J_3 = `J_3
    J_4 = `J_4
    I_v = `I_v
    I_h = `I_h
    S_d = `S_d
    S_u = `S_u
    Z_d = `Z_d
    Z_u = `Z_u
    State = `S9 + `S14
    board = `S9 -> 0 -> (0 + 1) -> `True + `S9 -> 1 -> 1 -> `True
      + `S9 -> 0 -> (2 + 3) -> `False + `S9 -> 1 -> (0 + 2 + 3) -> `False
      + `S9 -> (2 + 3) -> (0 + 1 + 2 + 3) -> `False
      + `S14 -> 0 -> 0 -> `True + `S14 -> (1 + 2) -> 1 -> `True
      + `S14 -> 0 -> (1 + 2 + 3) -> `False + `S14 -> (1 + 2) -> (0 + 2 + 3) -> `False
      + `S14 -> 3 -> (0 + 1 + 2 + 3) -> `False 
    nexts = `S9 -> `S14
    nextp = `S9 -> `Z_d
  }
}