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
  boardBounds: assert checkBounds is necessary for wellformed_states

  oneTerminal: assert { 
    one t: State | {
      no t.nexts and no t.nextp
      all s: State | (s != t) implies (some s.nexts and some s.nextp)
    }
  } is necessary for wellformed_states for exactly 4 State

  oneInitialContinuous: assert { 
    wellformed_states
    one i: State | {
      all s: State | (s != i) implies reachable[s,i,nexts]
    }
  } is sat for exactly 4 State

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
  
}

test suite for wellformed_game {
  example thing is {wellformed_game} for {
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
      + `S1 -> (1 + 2 + 3) -> (1 + 2 + 3) -> `False
      + `S2 -> 0 -> (0 + 1) -> `True + `S2 -> 1 -> 0 -> `True 
      + `S2 -> (2 + 3) -> (0 + 1 + 2 + 3) -> `False 
      + `S2 -> 1 -> (1 + 2 + 3) -> `False + `S2 -> 0 -> (2 + 3) -> `False 
    nexts = `S1 -> `S2
    nextp = `S1 -> `L_3
  }
}