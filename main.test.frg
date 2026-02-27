#lang forge

open "setup.frg"
open "main.frg"

pred checkBounds {
  all s: State | {
    all x, y: Int | some s.board[x,y] implies {
      x >= 0 and x <= 3
      y >= 0 and y <= 3
    }
  }
}

test suite for wellformed_states {
  // the board is always within the correct bounds
  boardBounds: assert checkBounds is necessary for wellformed_states

  // each state has exactly 3 cells filled
  threeCellsFilled: assert {
    all s: State | {
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
  } is necessary for wellformed_states for exactly 4 State

  // there is a unique terminal state
  oneTerminal: assert { 
    one t: State | {
      no t.nexts and no t.nextp
      all s: State | (s != t) implies (some s.nexts and some s.nextp)
    }
  } is necessary for wellformed_states for exactly 4 State

  // there is a unique initial state from which all other states are reachable
  oneInitialContinuous: assert { 
    one i: State | {
      all s: State | (s != i) implies reachable[s,i,nexts]
    }
  } is necessary for wellformed_states for exactly 4 State

  // no state refers to itself
  noSelfLoop: assert {
    all s: State | s.nexts != s
  } is necessary for wellformed_states for exactly 4 State

  // there cannot be an isolated state
  example isolatedState is {checkBounds and not wellformed_states} for {
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
    State = `S1 + `S2 + `S3
    board = `S1 -> (0 + 1 + 2) -> 0 -> `True + `S1 -> 3 -> 0 -> `False 
      + `S1 -> (0 + 1 + 2 + 3) -> (1 + 2 + 3) -> `False
      + `S2 -> (1 + 2 + 3) -> 0 -> `True + `S2 -> 0 -> 0 -> `False 
      + `S2 -> (0 + 1 + 2 + 3) -> (1 + 2 + 3) -> `False
      + `S3 -> (0 + 2 + 3) -> 0 -> `True + `S3 -> 1 -> 0 -> `False 
      + `S3 -> (0 + 1 + 2 + 3) -> (1 + 2 + 3) -> `False
    nexts = `S1 -> `S2
    nextp = `S1 -> `J_3 + `S2 -> `I_h
  }
}

test suite for transition_clear {
  // for all transitions, the piece is placed in empty cells within the board
  pieceWithinBoard: assert {
    all pre, post: State | some pre.nextp and transition_clear[pre, post] implies {
      some x, y: Int | {
        next_piece_hole[x, y, pre]
        all p, q: Int | ((p -> q) in piece_coords[x, y, pre.nextp]) implies {
          p >= 0 and p <= 3 and q >= 0 and q <= 3
        }
      }
    }
  } is sat for exactly 4 State

  // transitioning on a horizontal I piece does not change the board
  boardSameI_h: assert {
    all pre, post: State | pre.nextp = I_h and transition_clear[pre, post] implies {
      all x, y: Int | (x >= 0 and x <= 3 and y >= 0 and y <= 3) implies {
        pre.board[x,y] = post.board[x,y]
      }
    }
  } is sat for exactly 4 State

  // random valid 2-state game
  example s9s14_Z_d_hole is {some disj s1, s2: State | transition_clear[s1, s2]} for {
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

  // random valid 2-state game
  example s2s5_via_l3_T is {some disj s1, s2: State | transition_clear[s1, s2]} for {
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
    State = `S1 + `S2
    board = `S1 -> 0 -> (0 + 1 + 2) -> `True + `S1 -> 0 -> 3 -> `False 
      + `S1 -> (1 + 2 + 3) -> (0 + 1 + 2 + 3) -> `False
      + `S2 -> 0 -> (0 + 1) -> `True + `S2 -> 1 -> 0 -> `True 
      + `S2 -> (2 + 3) -> (0 + 1 + 2 + 3) -> `False 
      + `S2 -> 1 -> (1 + 2 + 3) -> `False + `S2 -> 0 -> (2 + 3) -> `False 
    nexts = `S1 -> `S2
    nextp = `S1 -> `L_3
  }
}

test suite for wellformed_game {
  // state properties are unique
  noDuplicateStates: assert {
      all disj s1, s2: State | (all x, y: Int | s1.board[x,y] = s2.board[x,y]) implies 
        (s1.nextp != s2.nextp or s1.nexts != s2.nexts)
    } is necessary for wellformed_game for exactly 4 State

  // cycles are not allowed
  example cyclicStates is {not wellformed_game} for {
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
    State = `S1 + `S2
    board = `S1 -> 0 -> 0 -> `False + `S2 -> 0 -> 0 -> `False
    nexts = `S1 -> `S2 + `S2 -> `S1
    nextp = `S1 -> `O + `S2 -> `O
  }

  // random valid 2-state game
  example s2s5_via_l3_G is {wellformed_game} for {
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
    State = `S1 + `S2
    board = `S1 -> 0 -> (0 + 1 + 2) -> `True + `S1 -> 0 -> 3 -> `False 
      + `S1 -> (1 + 2 + 3) -> (0 + 1 + 2 + 3) -> `False
      + `S2 -> 0 -> (0 + 1) -> `True + `S2 -> 1 -> 0 -> `True 
      + `S2 -> (2 + 3) -> (0 + 1 + 2 + 3) -> `False 
      + `S2 -> 1 -> (1 + 2 + 3) -> `False + `S2 -> 0 -> (2 + 3) -> `False 
    nexts = `S1 -> `S2
    nextp = `S1 -> `L_3
  }
}