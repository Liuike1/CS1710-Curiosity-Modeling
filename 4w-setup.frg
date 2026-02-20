#lang forge/froglet

sig Mino {
  x: lone Int,
  y: lone Int
}

abstract sig Piece {}
one sig O extends Piece {}
abstract sig T extends Piece {}
one sig T_1 extends T {}
one sig T_2 extends T {}
one sig T_3 extends T {}
one sig T_4 extends T {}
abstract sig I extends Piece {}
one sig I_v extends I {}
one sig I_h extends I {}
abstract sig J extends Piece {}
one sig J_1 extends J {}
one sig J_2 extends J {}
one sig J_3 extends J {}
one sig J_4 extends J {}
abstract sig L extends Piece {}
one sig L_1 extends L {}
one sig L_2 extends L {}
one sig L_3 extends L {}
one sig L_4 extends L {}
abstract sig S extends Piece {}
one sig S_l extends S {}
one sig S_r extends S {}
abstract sig Z extends Piece {}
one sig Z_l extends Z {}
one sig Z_r extends Z {}

sig State {
  board: pfunc Int -> Int -> Boolean,
  nexts: lone State,
  nextp: lone Piece
}

pred o_piece[x, y: Int, s: State] {
  s.board[x,y] = False
  s.board[x+1,y] = False
  s.board[x,y+1] = False
  s.board[x+1,y+1] = False
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
    post.board[0,y] = pre.board[0,y+1]
    post.board[1,y] = pre.board[1,y+1]
    post.board[2,y] = pre.board[2,y+1]
    post.board[3,y] = pre.board[3,y+1]
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