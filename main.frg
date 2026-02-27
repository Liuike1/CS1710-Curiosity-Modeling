#lang forge

open "setup.frg"

pred wellformed_states {
  // all board states are continuable
  all s: State | {
    all x, y: Int | {
      (0 <= x and x <= 3 and 0 <= y and y <= 2) implies some s.board[x,y]
      (0 <= x and x <= 3 and y = 3) implies s.board[x,y] = False
      not (0 <= x and x <= 3 and 0 <= y and y <= 3) implies no s.board[x,y]
    }
    isShape1[s] or isShape1Mirror[s] or isShape2[s] or isShape2Mirror[s] 
    or isShape3[s] or isShape3Mirror[s] or isShape4[s] or isShape4Mirror[s] 
    or isShape5[s] or isShape5Mirror[s] or isShape6[s] or isShape6Mirror[s] 
    or isShape7[s] or isShape7Mirror[s] or isShape8[s] or isShape8Mirror[s] 
    or isShape9[s] or isShape9Mirror[s] or isShape10[s] or isShape10Mirror[s] 
    or isShape11[s] or isShape11Mirror[s] or isShape12[s] or isShape12Mirror[s] 
    or isShape13[s] or isShape13Mirror[s] or isShape14[s] or isShape14Mirror[s]
  }

  // only one board state is allowed to not have the next fields (i.e. it's the terminal state)
  one t: State | {
    no t.nexts and no t.nextp

    // all other board states must have all fields
    all s: State | (s != t) implies (some s.nexts and some s.nextp)
    
    // linearity
    all disj s1, s2: State | (s1 != t and s2 != t) implies {
      s1.nexts != s2.nexts
    }
  }

  // there is a unique starting state
  one i: State | {
    all s: State | (s != i) implies reachable[s,i,nexts]
  }
}

// checking that there is somewhere to put the next piece
pred next_piece_hole[x, y: Int, s: State] {
  s.nextp = O implies o_hole[x,y,s]

  s.nextp = T_1 implies t1_hole[x,y,s]
  s.nextp = T_2 implies t2_hole[x,y,s]
  s.nextp = T_3 implies t3_hole[x,y,s]
  s.nextp = T_4 implies t4_hole[x,y,s]

  s.nextp = L_1 implies l1_hole[x,y,s]
  s.nextp = L_2 implies l2_hole[x,y,s]
  s.nextp = L_3 implies l3_hole[x,y,s]
  s.nextp = L_4 implies l4_hole[x,y,s]

  s.nextp = J_1 implies j1_hole[x,y,s]
  s.nextp = J_2 implies j2_hole[x,y,s]
  s.nextp = J_3 implies j3_hole[x,y,s]
  s.nextp = J_4 implies j4_hole[x,y,s]

  s.nextp = I_v implies i_vert_hole[x,s]
  s.nextp = I_h implies i_horz_hole[y,s]

  s.nextp = S_d implies s_down_hole[x,y,s]
  s.nextp = S_u implies s_up_hole[x,y,s]

  s.nextp = Z_d implies z_down_hole[x,y,s]
  s.nextp = Z_u implies z_up_hole[x,y,s]
}

// Transition predicate: validates a valid piece placement and line clear
pred transition_clear[pre: State, post: State] {
  pre.nexts = post
  
  // find the coordinate to place the piece
  some x, y: Int | {
    // the next piece has somewhere to be placed
    x >= 0 and x <= 3 and y >= 0 and y <= 3
    next_piece_hole[x, y, pre]

    // the next piece is within bounds
    all s, t: Int | (s -> t) in piece_coords[x, y, pre.nextp] implies {
      s >= 0 and s <= 3 and t >= 0 and t <= 3
    }
    
    // the next piece is not floating
    some p, q: Int | {
      (p >= 0 and p <= 3 and q >= 0 and q <= 3) 
      (p -> q) in piece_coords[x, y, pre.nextp]
      (q = 0 or pre.board[p, subtract[q,1]] = True)
    }

    // find row that is cleared
    some clear_y: Int | {
      (clear_y >= 0 and clear_y <= 2)
      
      all check_x: Int | {
        (check_x >= 0 and check_x <= 3) implies {
          // Cell is True if it was True in pre OR piece occupies it
          pre.board[check_x,clear_y] = True or { 
            (check_x -> clear_y) in piece_coords[x, y, pre.nextp]
          }
        }
      }
      
      // check board below the cleared line stays the same, and board above moves down 1
      all x2, y2: Int | {
        (x2 >= 0 and x2 <= 3 and y2 >= 0 and y2 <= 3) implies {
          (y2 < clear_y) implies {
            // stays the same plus any possible mino from the new piece
            ((x2 -> y2) in piece_coords[x, y, pre.nextp]) implies {
              post.board[x2,y2] = True
            } else post.board[x2,y2] = pre.board[x2,y2] 
          }

          (y2 >= clear_y) implies {
            // moves down one plus any possible mino from new piece
            ((x2 -> add[clear_y,1]) in piece_coords[x, y, pre.nextp]) implies {
              post.board[x2,y2] = True
            } else post.board[x2,y2] = pre.board[x2,add[clear_y,1]]
          }
        }
      }
    }
  }
}

pred wellformed_game {
  wellformed_states
  all s: State | some s.nexts implies {
    transition_clear[s, s.nexts]
  }
}

test3: run {
  wellformed_game
  no s: State | s.nextp = I_h
} for exactly 4 State