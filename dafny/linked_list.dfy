// Successfully verified with [Dafny 3.3.0.31104] in little time.

// A simple implementation of the linked list, with a non-trivial operation:
// splitting it into two lists.
//
// Not that fancy, but it was a good practice of framing (the reads/modifies stuff).
// Made me appreciate how unsafe pointer manipulations are!!
// Even for such a simple data structure, so many things can potentially go wrong
// (with either insufficient or overly-strict specs).

class Node<T> {
  var val: T;
  var next: Node?<T>;

  constructor (val': T, next': Node?<T>)
    ensures val == val' && next == next'
  {
    val, next := val', next';
  }
}

class Linked<T> {
  var head: Node?<T>;
  ghost var s: seq<Node<T>>; // sequence repr of the linked list

  static predicate valid_sub(n: Node?<T>, s': seq<Node<T>>)
    reads s'
    decreases s'
  {
    if n == null then
      |s'| == 0
    else
      |s'| > 0 && n == s'[0] && valid_sub(n.next, s'[1..])
  }

  predicate valid()
    reads this, s
  {
    valid_sub(head, s)
  }

  constructor ()
  // construct an empty list
    ensures valid()
    ensures |s| == 0
  {
    head, s := null, [];
  }

  constructor from_seq(vals: seq<T>)
  // build the list from a sequence of values
    ensures valid()
    ensures |s| == |vals|
    ensures forall i :: 0 <= i < |s| ==> s[i].val == vals[i]
    ensures fresh(s)
  {
    var head': Node?<T> := null;
    ghost var s': seq<Node<T>> := [];

    var i := |vals| - 1;
    while i >= 0 // build the list reversely:
      invariant |s'| == |vals| - i - 1
      invariant i >= -1
      invariant forall j :: i < j < |vals| ==> s'[j-i-1].val == vals[j]
      invariant valid_sub(head', s')
      invariant fresh(s')
    {
      head' := new Node(vals[i], head');
      s' := [head'] + s';
      i := i - 1;
    }
    head, s := head', s';
  }

  static function method to_seq_sub(n': Node?<T>, ghost s': seq<Node<T>>): (vals: seq<T>)
    reads s'
    requires valid_sub(n', s')
    ensures |s'| == |vals|
    ensures forall i :: 0 <= i < |s'| ==> s'[i].val == vals[i]
  {
    if n' == null then
      []
    else
      [n'.val] + to_seq_sub(n'.next, s'[1..])
  }

  function method to_seq(): (vals: seq<T>)
    reads this, s
    requires valid()
    ensures |s| == |vals|
    ensures forall i :: 0 <= i < |s| ==> s[i].val == vals[i]
  {
    to_seq_sub(head, s)
  }

  predicate valid_alt()
  // an alternative, non-recursive validity criterion
    reads this, s
  {
    var last := |s| - 1;
    // either empty list:
    (head == null && |s| == 0) ||
    // or nonempty list, head == s[0] --> s[1] --> ... --> s[last] --> null:
    (|s| > 0 && head == s[0] && s[last].next == null &&
      forall i :: 0 <= i < last ==> s[i].next == s[i+1])
  }

  lemma ValidAlt_Compatible()
    ensures valid() <==> valid_alt()
  {
    assert valid() ==> valid_alt() by {
      assume valid();
      if |s| > 0 {
        var i, curr := 0, head;
        while i < |s|
          invariant i <= |s|;
          invariant valid_sub(curr, s[i..])
          invariant forall j :: 0 <= j < i ==> (s[j].next == if j+1 < |s| then s[j+1] else null)
          invariant i > 0 ==> s[i-1].next == if i < |s| then s[i] else null
        {
          i, curr := i + 1, curr.next;
        }
      }
    }
    assert valid_alt() ==> valid() by {
      assume valid_alt();
      if |s| > 0 {
        var i := |s|-1;
        while i > 0
          invariant 0 <= i <= |s|-1;
          invariant valid_sub(s[i], s[i..])
        {
          i := i - 1;
        }
      }
    }
  }

  lemma ElementsAreDistinct_Intros(i: int, j: int)
    requires valid_alt()
    requires 0 <= i < j < |s|
    ensures s[i] != s[j]
    decreases |s| - j
  {
    if j == |s| - 1 {
      assert s[i].next == s[i+1] && s[j].next == null;   
    } else {
      ElementsAreDistinct_Intros(i+1, j+1);
    }
  }

  lemma ElementsAreDistinct()
    requires valid()
    ensures forall i, j :: 0 <= i < j < |s| ==> s[i] != s[j]
  {
    ValidAlt_Compatible();
    forall i, j | 0 <= i < j < |s| {
      ElementsAreDistinct_Intros(i, j);
    }
  }

  method split(n: Node<T>) returns (l: Linked<T>, r: Linked<T>)
  // Splits the list into two (l and r) where n is the tail of l.
    requires valid()
    requires n in s
    modifies this`s, n`next
    ensures l.valid() && r.valid()
    ensures l == this && fresh(r)
    ensures l.s + r.s == old(s) && |l.s| > 0 && l.s[|l.s|-1] == n
  {
    ValidAlt_Compatible();
    ghost var i :| 0 <= i < |s| && s[i] == n; // let i be the index of n
    // get the right half:
    r := new Linked();
    r.head := n.next;
    r.s := s[i+1 ..];
    assert r.valid() by {
      r.ValidAlt_Compatible();
    }
    // get the left half:
    assert n !in r.s by { // make sure that modifying n will not influence r:
      ElementsAreDistinct();
    }
    assert n !in s[..i] by { // and that it will not influence its precessors:
      ElementsAreDistinct();
    }
    n.next := null;
    l := this;
    l.s := s[.. i+1];
    assert l.valid() by {
      l.ValidAlt_Compatible();
    }
  }
}


method test()
{
  var a := new Linked<int>();
  assert a.head == null;
  var s := a.to_seq();
  assert s == [];

  var b := new Linked.from_seq([1,2,3,4]);
  assert b.head.val == 1;
  assert Linked.valid_sub(b.head.next, b.s[1..]);
  assert b.head.next != null;
  assert b.head.next.val == 2;
  var t := b.to_seq();
  assert t == [1,2,3,4];

  var h := b.head;
  assert h.next in b.s;
  var c, d := b.split(h);
  var u := c.to_seq();
  var v := d.to_seq();
  assert c.head.val == 1;
  c.ValidAlt_Compatible();
  assert c.head.next == null;
  assert u == [1];
  assert v == [2,3,4];
}