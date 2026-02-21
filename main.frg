#lang forge/froglet

open "setup.frg"

pred wellFormed[s: State]{
    isShape1[s] or isShape1Mirror[s] or isShape2[s] or isShape2Mirror[s] or
    isShape3[s] or isShape3Mirror[s] or isShape4[s] or isShape4Mirror[s] or
    isShape5[s] or isShape5Mirror[s] or isShape6[s] or isShape6Mirror[s] or
    isShape7[s] or isShape7Mirror[s] or isShape8[s] or isShape8Mirror[s] or
    isShape9[s] or isShape9Mirror[s] or isShape10[s] or isShape10Mirror[s] or
    isShape11[s] or isShape11Mirror[s] or isShape12[s] or isShape12Mirror[s] or
    isShape13[s] or isShape13Mirror[s] or isShape14[s] or isShape14Mirror[s]
}

test2: run {some s1, s2: State | {
        s1 != s2
        wellFormed[s1]
        wellFormed[s2]
    }} for exactly 2 State



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

// pred continuable[s: State] {
//   s.next 
// }