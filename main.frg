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