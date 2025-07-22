# Harry's 3 Variable Example

## Definition

Initial State:

* a & b & c

Transitions:

* a' <=> a
* b' <=> (a & c) | (~a & b)
* c' <=> ~a | ~b

Safety Property:

* a | ~c

## Transform to use only AND and NOT

Initial State:

* a & b & c

Transitions:

* a' <=> a
* b' <=> ~(~(a & c) & ~(~a & b))
* c' <=> ~(a & b)

Safety Property:

* ~(~a & c)

## Into AIG

Latches:

a=0
b=0
c=0

No Inputs:

Output:

~P : ~a & c

Gates:

## AIGER file
aag 18 0 3 1 5
2 2 0           // latch a
4 19 0          // latch b
8 13 0          // latch c
10              // safety property
10 3 8          // P = ~a & c
12 2 4          // a & b
14 2 8          // a & c
16 3 4          // ~a & b
18 15 17        // ~(a & c) & ~(~a & b)
