// This is a more humanly-intuitive version of the "dp_stairs" puzzle.
// The logic should feel close to what you really think when you work on the puzzle,
// except you may even skip some "just-so-intuitive" reasoning that Dafny does not.

// Original puzzle:
/// How many different ways are there to climb (n: nat) stairs
/// if you can climb either 1 or 2 stairs at each step?
/// e.g.
/// There is 1 way to climb 0 stairs: using 0 steps.
/// There is 2 way to climb 2 stairs: [1,1] or [2].

// Successfully verified with [Dafny 3.3.0.31104] in about 5 seconds.


// Starting with 3 simple definitions to make the code more readable:
function sum(s: seq<nat>): nat {
  if s == [] then 0 else s[0] + sum(s[1..])
}

predicate legal(move: seq<nat>, height: nat) {
  (forall i :: 0 <= i < |move| ==> move[i] in {1, 2}) &&
  sum(move) == height
}

predicate valid_set(moves: set<seq<nat>>, height: nat) {
  forall move :: legal(move, height) <==> move in moves
}


// When I say it's an intuitive proof I mean it.
// You can look at this function's code and rephrase it in plain English!
function count_moves(height: nat): (count: nat)
  ensures exists moves :: valid_set(moves, height) && count == |moves|
{
  if height == 0 then
    ghost var moves: set<seq<nat>> := {[]};
    assert valid_set(moves, 0) by {
      // forall move | move in moves ensures legal(move, 0) {}
      // forall move | legal(move, 0) ensures move in moves {}
    }
    1

  else if height == 1 then
    ghost var moves: set<seq<nat>> := {[1]};
    assert valid_set(moves, 1) by {
      // forall move | move in moves ensures legal(move, 1) {}
      forall move | legal(move, 1) ensures move in moves {
        // if |move| == 0 { assert !legal(move, 1); }
        if |move| == 1 { assert move == [1] || move == [2]; assert !legal([2], 1); }
        if |move| >= 2 { assert sum(move) >= 2; }
      }
    }
    1

  else
    var count_1, count_2 := count_moves(height - 1), count_moves(height - 2);
    ghost var moves_1 :| valid_set(moves_1, height - 1) && count_1 == |moves_1|;
    ghost var moves_2 :| valid_set(moves_2, height - 2) && count_2 == |moves_2|;

    ghost var moves_1' := set move | move in moves_1 :: [1] + move;
    assert |moves_1'| == |moves_1| by {
      forall move' ensures ([1] + move')[1..] == move' {}
      Injective_Same_Size(moves_1, moves_1', move => [1] + move);
    }

    ghost var moves_2' := set move | move in moves_2 :: [2] + move;
    assert |moves_2'| == |moves_2| by {
      forall move' ensures ([2] + move')[1..] == move' {}
      Injective_Same_Size(moves_2, moves_2', move => [2] + move);
    }

    ghost var moves := moves_1' + moves_2';
    assert moves_1' !! moves_2' by {
      forall m1, m2 | m1 in moves_1' && m2 in moves_2' ensures m1 != m2 {
        assert m1[0] == 1 && m2[0] == 2;
      }
    }
    assert valid_set(moves, height) by {
      // forall move | move in moves ensures legal(move, height) {}
      forall move | legal(move, height) ensures move in moves {
        if move[0] == 1 { assert move[1..] in moves_1 && move == [1] + move[1..]; }
        if move[0] == 2 { assert move[1..] in moves_2 && move == [2] + move[1..]; }
      }
    }
    count_1 + count_2
}


// Below are some lemmas used for proof.
// They are very "intuitive facts" to human, but Dafny seems to be unfamiliar with them.

// Human intuitively know this fact;
// luckly Dafny can realize it with just a little hint!
lemma Injective_Same_Size<T, U> (s: set<T>, s': set<U>, op: T -> U)
  requires s' == set elem | elem in s :: op(elem)
  requires forall e1, e2 :: op(e1) == op(e2) ==> e1 == e2
  ensures |s'| == |s|
{
  if elem :| elem in s {
    Injective_Same_Size(s - {elem}, s' - {op(elem)}, op);
  }
}