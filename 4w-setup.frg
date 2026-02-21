#lang forge/froglet

abstract sig Boolean {}
one sig True, False extends Boolean {}

abstract sig Piece {}
abstract sig T, I, L, J, S, Z extends Piece {}

one sig O extends Piece {}
one sig T_1, T_2, T_3, T_4 extends T {}
one sig I_v, I_h extends I {}
abstract sig J extends Piece {}
one sig L_1, L_2, L_3, L_4 extends L {}
one sig J_1, J_2, J_3, J_4 extends J {}
one sig S_d, S_u extends S {}
one sig Z_d, Z_u extends Z {}

sig State {
  board: pfunc Int -> Int -> Boolean,
  nexts: lone State,
  nextp: lone Piece
}



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

pred transition_helper[pre: State, post: State] {
  // pre.nextp = O implies {
  //   some disj x, y: Int | o_piece[x,y,pre]
  //  }
  // implies {
    some y: Int | line_clear[y, pre]
    post.board[0,y] = pre.board[0,add[y,1]]
    post.board[1,y] = pre.board[1,add[y,1]]
    post.board[2,y] = pre.board[2,add[y,1]]
    post.board[3,y] = pre.board[3,add[y,1]]
  // }
  // post = fail
}

// pred game_wellformed {all s: State | transition_helper[s, s.next, bag]}
// for exactly 10 State 2 Bag

pred wellformed {
  all s: State | {
    some disj m1, m2, m3: Mino | {
      s.board[m1.x,m1.y] = m1
      s.board[m2.x,m2.y] = m2
      s.board[m3.x,m3.y] = m3
      all x, y: Int | ((x != m1.x or y != m1.y) and (x != m2.x or y != m2.y) 
        and (x != m3.x or y != m3.y)) => {
        no s.board[x,y]
      }
    }
  }
}

// pred continuable[s: State] {
//   s.next 
// }