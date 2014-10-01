# Boogie programs automatically generated from Brainfuck programs.

Author: Jan Leike
Date: 2014-08-18


## About

This directory should contain all Brainfuck programs of length at most 6
that do not terminate within 100 steps.
All of these programs are suspected to be nonterminating.

Note that due to the filesystem limitations on some operating systems,
we use d and b instead of < and > in the filenames.


## Brainfuck

Uses the standard Brainfuck instructions except for input ',' and output '.':

    < > + - [ ]

https://en.wikipedia.org/wiki/Brainfuck#Commands

The memory model is an list of unsigned natural numbers of unbounded size.
* The list is infinite to the right but not the left.
* The head starts at the left-most cell.
* Underflow yields 0.
* Non-matched opening bracket matches at the program end.
* Non-matched closing bracket matches at the program start.


## Generation Procedure

These files were generated according to the following procedure:
* List all strings composed of the six characters <>+-[] and for each do:
* Run the corresponding Brainfuck program for 100 steps
* If it has not terminated,
  translate it to Boogie code and dump it to a file.

