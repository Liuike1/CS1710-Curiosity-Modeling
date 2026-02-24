# Curiosity Modeling - Tetris 4W 

# Project Objective

This project models the problem of "4-widing" in modern guideline Tetris ([you can read more here!](https://four.lol/stacking/4-wide)). Essentially, the goal is to continue combo in a 4 grid wide gap for as long as possible under the modern Tetris ruleset. 

We will NOT be modeling the actual game, instead, our model will be a checker to see if a given piece sequence can successfully continue the combo given a starting state. 

# Design

We designed the model as a continuous chain of states, of which all except one has a next state, with that specifc state being the final state. Since 4-widing only cares about a 3x4 subset of the 10x20 board, each of our states will only have the 3x4 portion that matters. 

Since the "use case" is to check given a piece sequence and start state, whether a player can continue the combo, we only modeled the 28 distinct continuable board states. 

# Visualization

TBD

# Signature and Predicates

## Pieces Sig

We wrote signatures for each distinct rotation for each piece, i.e. 4 rotations for L/J piece, 2 for S/Z piece, and 1 for O piece. 

## States Sig

Each state represents a 3x4 board state, with a pfunc mapping row,col to True/False, representing whether a mino exists at that coordinate, and also a next state and next piece. 

## Boolearn Sig

We used the same True/False signatures used in other projects. 

## State Pred

We wrote predicates for each of the 28 continuable states, checking if a given state matches that exact configuration of minos. 

## Wellformed Pred

The well formed predicate checks that each coordinate in a state is mapped to exactly one of True/False. It also checks that only one state can not have a next state and next piece, which acts as the last state. 

Since we only care about the continuable states, we also check that all states satisfy one of the 28 state predicates

## Transition Pred

TBD

# Testing

TBD

# Documentation

Embedded?
