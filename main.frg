#lang forge

open "setup.frg"

pred wellformed_state[s: State] {
  some s.nextp
  // some s.nexts
  all x, y: Int | {
    (0 <= x and x <= 3 and 0 <= y and y <= 2) implies some s.board[x,y] else no s.board[x,y]
  }
  (isShape1[s] or isShape1Mirror[s] or isShape2[s] or isShape2Mirror[s] 
    or isShape3[s] or isShape3Mirror[s] or isShape4[s] or isShape4Mirror[s] 
    or isShape5[s] or isShape5Mirror[s] or isShape6[s] or isShape6Mirror[s] 
    or isShape7[s] or isShape7Mirror[s] or isShape8[s] or isShape8Mirror[s] 
    or isShape9[s] or isShape9Mirror[s] or isShape10[s] or isShape10Mirror[s] 
    or isShape11[s] or isShape11Mirror[s] or isShape12[s] or isShape12Mirror[s] 
    or isShape13[s] or isShape13Mirror[s] or isShape14[s] or isShape14Mirror[s])
}

test2: run {
  some s1, s2: State | {
    s1 != s2
    wellformed_state[s1]
    wellformed_state[s2]
  }
} for exactly 2 State

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

  s.nextp = I_v implies i_vert_hole[x,y,s]
  s.nextp = I_h implies i_horz_hole[x,y,s]

  s.nextp = S_d implies s_down_hole[x,y,s]
  s.nextp = S_u implies s_up_hole[x,y,s]

  s.nextp = Z_d implies z_down_hole[x,y,s]
  s.nextp = Z_u implies z_up_hole[x,y,s]
}

// fun line_clear[x, y: Int, s: State]: Int -> Int {
//   next_piece_hole[x,y,s]
// }

// pred transition_clear[pre: State, post: State] {
//   some disj x, y: Int | {
//     next_piece_hole[x,y,pre]
//   }
// }
/**
some y: Int | line_clear[y, pre] implies {
      post.board[0,y] = pre.board[0,add[y,1]]
    post.board[1,y] = pre.board[1,add[y,1]]
    post.board[2,y] = pre.board[2,add[y,1]]
    post.board[3,y] = pre.board[3,add[y,1]]
    }
*/

pred wellformed_game {
  all s: State | {
    wellformed_state[s]
   // some t: State | t = s.nexts implies transition_clear[s,t]
   // not reachable[s, s, nexts]
  }
}

test3: run {
  wellformed_game
} for exactly 4 State