// An "easy" dynamic programming puzzle, but its proof was not that trivial!
// Successfully verified with [Dafny 3.3.0.31104] in about 5 seconds.

// How many different ways are there to climb (n: nat) stairs
// if you can climb either 1 or 2 stairs at each step?
// e.g.
// There is 1 way to climb 0 stairs: using 0 steps.
// There is 2 way to climb 2 stairs: [1,1] or [2].
//
// We can use dynamic programming, but we need proof.


// We say a finite sequence s "enumerates" a property P, iff
// elements in s are "correct, distinct, complete".
predicate enumerates<T(!new)>(s: seq<T>, P: T -> bool) {
  (forall x :: x in s ==> P(x)) && // A
  (forall i, j :: 0 <= i < j < |s| ==> s[i] != s[j]) && // B
  (forall x :: P(x) ==> x in s) // C
}

// We use a seq of nats to represent a "legal way to climb".
function sum(s: seq<nat>): nat {
  if s == [] then 0 else s[0] + sum(s[1..])
}

predicate legal(s: seq<nat>, height: nat) {
  (forall x :: x in s ==> x in {1, 2}) &&
  sum(s) == height
}

// Just some simple tests to verify our definition:
lemma one_way_0_stair()
  ensures enumerates([[]], s => legal(s, 0))
{
  // A and B are quite straightforward. For C:
  forall steps | legal(steps, 0) ensures steps == [] {
    if |steps| > 0 { // hint a contradiction:
      assert steps[0] in steps;
    }
  }
}

lemma one_way_1_stair()
  ensures enumerates([[1]], s => legal(s, 1))
{
  // A and B are still straightforward.
  // C is followed by some tedious case study, given some hints:
  forall steps | legal(steps, 1) ensures steps == [1] {
    forall i | 0 <= i < |steps| ensures steps[i] >= 1 {
      assert steps[i] in steps;
    }
    if |steps| == 0 {
      assert sum(steps) == 0;
    }
    if |steps| == 1 {
      if steps[0] != 1 { assert sum(steps) >= 2; }
    }
    if |steps| >= 2 {
      assert sum(steps) >= 2;
    }
  }
}

// We can now represent the spec of the problem:
/* 
method count_ways_to_climb(height: nat) returns (count: nat)
  ensures exists s :: |s| == count &&
    enumerates(s, steps => legal(steps, height))
*/


// To use DP, an important insight is the below relation:
function ways(height: nat): seq<seq<nat>> {
  if height == 0 then
    [[]]
  else if height == 1 then
    [[1]]
  else
    foreach(ways(height-1), steps => [1] + steps) +
    foreach(ways(height-2), steps => [2] + steps)
}
// where `foreach` is defined as:
function {:opaque} foreach<T, U>(s: seq<T>, op: T -> U): (s': seq<U>)
/* fix: add `{:opaque}` to avoid Z3 running forever */
  ensures |s'| == |s|
  ensures forall i :: 0 <= i < |s| ==> s'[i] == op(s[i])
{
  if s == [] then
    []
  else
    [op(s[0])] + foreach(s[1..], op)
}

// We prove the validity of `ways` by induction:
lemma ways_valid(height: nat)
  ensures enumerates(ways(height), steps => legal(steps, height))
{
  if height == 0 { one_way_0_stair(); }
  if height == 1 { one_way_1_stair(); }
  if height >= 2 { // by induction:
    ways_valid(height - 2);
    ways_valid(height - 1);
    var P := steps => legal(steps, height); // P is the inductive invariant
    var w, w1, w2 := ways(height), ways(height-1), ways(height-2);
    assert forall steps :: steps in w ==> P(steps) by { // correctness:
      forall s1 | s1 in w1 ensures P([1] + s1) {}
      forall s2 | s2 in w2 ensures P([2] + s2) {}
    }
    assert forall i, j :: 0 <= i < j < |w| ==> w[i] != w[j] by { // distinctness:
      forall i, j | 0 <= i < j < |w1| ensures w[i] != w[j] {
        assert w[i][1..] != w[j][1..];
      }
      forall i, j | |w1| <= i < j < |w| ensures w[i] != w[j] {
        assert w[i][1..] != w[j][1..];
      }
      forall i, j | 0 <= i < |w1| <= j < |w| ensures w[i] != w[j] {
        assert w[i][0] == 1 && w[j][0] == 2;
      }
    }
    assert forall steps :: P(steps) ==> steps in w by { // completeness:
      forall s | P(s) ensures s[0] in s {}
      forall s | P(s) && s[0] == 1 ensures s in w {
        forall i | 0 <= i < |s[1..]| ensures s[1..][i] in s {}
        assert sum(s[1..]) == height - 1;
        assert legal(s[1..], height - 1);
        assert s[1..] in w1;
        assert s == [1] + s[1..];
      }
      forall s | P(s) && s[0] == 2 ensures s in w {
        forall i | 0 <= i < |s[1..]| ensures s[1..][i] in s {}
        assert sum(s[1..]) == height - 2;
        assert legal(s[1..], height - 2);
        assert s[1..] in w2;
        assert s == [2] + s[1..];
      }
    }
  }
}

// Okay, now all the heavy proofs are done!
//
// Note that we are only asked for the **count** of different ways but
// not the ways themselves!
// It means we can calculate the result in linear time.
function ways_count(height: nat): (count: nat)
  ensures count == |ways(height)|
{
  if height <= 1 then
    1
  else
    ways_count(height - 1) + ways_count(height - 2)
}

// Finally:
method count_ways_to_climb(height: nat) returns (count: nat)
  ensures exists s :: |s| == count && enumerates(s, steps => legal(steps, height))
{
  if height == 0 {
    ways_valid(0);
    return 1;
  }
  var c', c := 1, 1; // record previous and current count
  var h := 1; // recond the current height
  while h < height
    invariant h <= height
    invariant c' == ways_count(h-1) && c == ways_count(h)
  {
    c', c := c, c' + c;
    h := h + 1;
  }
  ways_valid(height);
  return c;
}

// TODO: there are even faster algorithms (involving matrix multiplication).
// Maybe next time!!