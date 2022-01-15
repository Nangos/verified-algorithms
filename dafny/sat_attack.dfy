// This is a mechanical verification of the `Algorithm 1` (SAT Attack) mentioned in:
// "Evaluating the Security of Logic Encryption Algorithms"
// See (https://cse.iitk.ac.in/users/spramod/papers/host15.pdf)
//
// The underlying SAT solver was implemented naively, but it was not the point.
// The method is opaque anyway, and only the specs matter.

// Successfully verified with [Dafny 3.3.0.31104] in 23 seconds (quite long time huh...)
// It was a fun practice for programming in Dafny, as it involved some cool language features.

abstract module SATMod {
  const bv_len: nat // the input length of the bit vector
  type bv = x: seq<bool> | |x| == bv_len witness seq(bv_len, i => false) // bit vector

  predicate SAT(circ: bv -> bool) {
    exists x :: circ(x) == true
  }

  method SolverSub(circ: bv -> bool, prefix: seq<bool>) returns (sat: bool, x: bv)
    requires |prefix| <= bv_len
    ensures sat ==> circ(x) == true
    ensures !sat ==> forall x :: x[..|prefix|] == prefix ==> circ(x) == false
    decreases bv_len - |prefix|
  {
    var len := |prefix|;
    if len == bv_len {
      sat, x := circ(prefix), prefix;
      assert x[..len] == x;
      assert !sat ==> forall x :: x == prefix ==> circ(x) == false;
    } else {
      var sat0, x0 := SolverSub(circ, prefix + [false]);
      if sat0 {
        return sat0, x0;
      }
      forall x | x[..len] == prefix && x[len] == false ensures circ(x) == false {}

      var sat1, x1 := SolverSub(circ, prefix + [true]);
      if sat1 {
        return sat1, x1;
      }
      forall x | x[..len] == prefix && x[len] == true ensures circ(x) == false {}
      return false, x0;
    }
  }

  method Solver(circ: bv -> bool) returns (sat: bool, x: bv)
    ensures sat ==> SAT(circ) && circ(x) == true
    ensures !sat ==> !SAT(circ)
  {
    sat, x := SolverSub(circ, []);
  }
}


abstract module AttackerMod refines SATMod {
  // parameter definitions:
  const pi_len: nat // primary input
  type pi = x: seq<bool> | |x| == pi_len witness seq(pi_len, i => false)
  const ki_len: nat // key input
  type ki = x: seq<bool> | |x| == ki_len witness seq(ki_len, i => false)
  const out_len: nat // output
  type out = x: seq<bool> | |x| == out_len witness seq(out_len, i => false)

  // parameter applications:
  const bv_len := pi_len + ki_len * 2 + 1 // for the mitter

  // the mitter circ used for SAT attack:
  function method Mitter(g: (pi, ki) -> out): (circ: bv -> bool) {
    (b: bv) => (
      var x, k0, k1, eq := get_x(b), get_k0(b), get_k1(b), get_eq(b);
      eq == (g(x, k0) == g(x, k1))
    )
  }

  // get parts from a bv seq:
  function method get_x(b: bv): pi { b[.. pi_len] }
  function method get_k0(b: bv): ki { b[pi_len .. pi_len + ki_len] }
  function method get_k1(b: bv): ki { b[pi_len + ki_len .. pi_len + ki_len * 2] }
  function method get_eq(b: bv): bool { b[pi_len + ki_len * 2] }

  function {:opaque} bv_from_subparts(x: pi, k0: ki, k1: ki, eq: bool): (b: bv)
    ensures get_x(b) == x && get_k0(b) == k0 && get_k1(b) == k1 && get_eq(b) == eq
  {
    x + k0 + k1 + [eq]
  }

  // Some properties about the keys:
  predicate key_correct(key: ki, g: (pi, ki) -> out, oracle: pi -> out) {
    forall x :: g(x, key) == oracle(x)
  }

  predicate key_equivalent(k0: ki, k1: ki, g: (pi, ki) -> out) {
    forall x :: g(x, k0) == g(x, k1)
  }

  lemma equivalent_correct(k0: ki, k1: ki, g: (pi, ki) -> out, oracle: pi -> out)
    ensures key_equivalent(k0, k1, g) ==>
      key_correct(k0, g, oracle) == key_correct(k1, g, oracle)
  {}

  // Next, we obtain the full set of bit vectors. It is a bit tricky...
  // Things like `set b: bv | true` wouldn't work, Dafny complains it may be infinite.
  // Don't know if there are more element ways to do this.
  function {:opaque} foreach<T, U>(s: seq<T>, op: T -> U): (s': seq<U>)
    ensures |s'| == |s|
    ensures forall i :: 0 <= i < |s| ==> s'[i] == op(s[i])
  {
    if s == [] then
      []
    else
      [op(s[0])] + foreach(s[1..], op)
  }

  function bv_power_set(len: nat): seq<seq<bool>> {
    if len == 0 then
      [[]]
    else
      var s := bv_power_set(len - 1);
      foreach(s, b => [false] + b) + foreach(s, b => [true] + b)
  }

  lemma bv_power_set_is_full_set(len: nat)
    ensures forall b :: |b| == len ==> b in bv_power_set(len)
  {
    if len > 0 {
      forall b | |b| == len ensures b in bv_power_set(len) {
        bv_power_set_is_full_set(len - 1);
        if b[0] == false {
          assert b == [false] + b[1..];
        } else {
          assert b == [true] + b[1..];
        }
      }
    }
  }

  // Finally, the SAT attack method:
  method SATAttack(g: (pi, ki) -> out, oracle: pi -> out) returns (key: ki)
    requires exists k :: key_correct(k, g, oracle)
    ensures key_correct(key, g, oracle)
  {
    // just to prove the while loop terminates, we maintain a set of candidate keys:
    ghost var candidates: set<ki> := set b | b in bv_power_set(ki_len);
    assert forall k :: k in candidates by {
      bv_power_set_is_full_set(ki_len);
    }
    // the circuit `legal` maintains the constraints on keys:
    var legal := (k: ki) => true;
    // the main `circ` is initialized as a mitter:
    var mitter := Mitter(g);
    var circ := mitter;
    // we obtain an arbitrary correct key, just from the pre-conditioned existence:
    ghost var k_star :| key_correct(k_star, g, oracle);

    while true
      invariant legal(k_star)
      invariant forall b :: circ(b) ==> (get_k0(b) in candidates && get_k1(b) in candidates)
      invariant forall b :: circ(b) <==> mitter(b) && legal(get_k0(b)) && legal(get_k1(b))
      decreases candidates
    {
      var circ' := (b: bv) => (
        circ(b) && get_eq(b) == false // we require the mittered g's are different
      );
      var sat, assignment := Solver(circ');
      if !sat { // it's time to break the loop, since all keys left are just equivalent:
        forall k0, k1 | legal(k0) && legal(k1) ensures key_equivalent(k0, k1, g) {
          if exists x :: g(x, k0) != g(x, k1) { // prove by contradiction
            ghost var x :| g(x, k0) != g(x, k1);
            ghost var b := bv_from_subparts(x, k0, k1, false);
            assert circ'(b);
          }
        }
        break;
      }
      // If sat, then we have found two disagreeing keys, at lease one of which is wrong:
      ghost var k0, k1 := get_k0(assignment), get_k1(assignment);
      var x' := get_x(assignment);
      assert g(x', k0) != g(x', k1);
      // (ghostly) eliminate the wrong keys from the candidates:
      var y' := oracle(x');
      if g(x', k0) != y' { candidates := candidates - {k0}; }
      if g(x', k1) != y' { candidates := candidates - {k1}; }

      // Update the constraints:
      legal := (k: ki) => (legal(k) && g(x', k) == y');
      circ := (b: bv) => (
        mitter(b) && legal(get_k0(b)) && legal(get_k1(b))
      );
    }

    // At this point, all keys left that satisfy `circ` are correct:
    var sat, assignment := Solver(circ);
    assert sat by { // prove by contructing a SAT assignment:
      var x: pi; // obtain an arbitrary x
      var b := bv_from_subparts(x, k_star, k_star, true);
      assert circ(b);
    }
    key := get_k0(assignment);
    // We just returned `key`. Below are proof that `key` is correct:
    assert key_equivalent(key, k_star, g);
    equivalent_correct(key, k_star, g, oracle);
  }
}
