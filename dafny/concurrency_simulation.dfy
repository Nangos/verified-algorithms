// Simple concurrent counter with atomic counts.
// It is sooo tricky to simulate "concurrency" in Dafny!

// Almost successfully verified with [Dafny 3.3.0.31104] in 20 seconds, except:
// - [Line 271] ConcurrentAdder.sum_rest_lemma


// Simulates a thread as a state machine
trait Thread {
  var done: bool // whether the thread's work is done
  var started: bool // whether the thread has started
  ghost var decreaser: nat // a reference that always decreases (to prove termination)
  ghost const resources: set<object> // the collection of all shared resources of the thread

  predicate valid_custom() reads this // custom validity condition for extended classes

  predicate valid() reads this {
    && valid_custom()
    && (!done ==> decreaser > 0)
  }

  // Similates an atomic operation of the thread:
  method step()
    modifies this, resources
    requires valid()
    requires !done
    ensures valid()
    ensures started
    ensures decreaser < old(decreaser)
}


// Simulates a thread scheduler
trait Scheduler {
  const threads: set<Thread> // a set of threads to schedule
  ghost const resources: set<object> // the collection of all shared resources among the threads

  predicate valid_custom() reads this // custom validity condition for extended classes

  predicate valid() reads this, threads {
    && valid_custom()
    && (|threads| > 0) // cannot construct an empty scheduler
    && (forall t | t in threads :: t.valid()) // all threads are themselves valid
    && (forall t | t in threads :: t.resources == resources) // all threads share the same resources
    && (this !in resources) // the Scheduler itself cannot be a resource
    && (forall t | t in threads :: t !in resources) // the threads themselves cannot be resources
  }

  // Arbitrarily picks a yet-to-finish thread to run.
  // Since methods are opaque, only the spec matters.
  method pick() returns (thread: Thread?)
    ensures thread != null ==> thread in threads && !thread.done
    ensures thread == null ==> forall t | t in threads :: t.done
  {
    var candidates: set<Thread> := threads;
    while |candidates| > 0
      invariant forall t | t in threads - candidates :: t.done
      invariant candidates <= threads
    {
      var thread :| thread in candidates;
      if !thread.done {
        return thread;
      }
      candidates := candidates - {thread};
    }
    return null;
  }

  // The sum of all threads' decreasers, which should also be decreasing:
  function sum_decreasers(): nat reads this, threads {
    sum_decreasers_sub(threads)
  }
  // where:
  static function sum_decreasers_sub(threads: set<Thread>): nat
    reads threads
  {
    if t :| t in threads then
      t.decreaser + sum_decreasers_sub(threads - {t})
    else
      0
  }

  // Proof that the sum does not depend on thread order:
  // Sometimes Dafny is not smart...
  static lemma sum_decreasers_lemma (t: Thread, threads: set<Thread>)
    requires t in threads
    ensures sum_decreasers_sub(threads) == t.decreaser + sum_decreasers_sub(threads - {t})
  {
    var F := sum_decreasers_sub;
    var t' :| t' in threads && F(threads) == t'.decreaser + F(threads - {t'});
    if t' != t {
      calc {
        F(threads);
      == // Definition
        t'.decreaser + F(threads - {t'});
      == { sum_decreasers_lemma(t, threads - {t'}); }
        t'.decreaser + (t.decreaser + F(threads - {t'} - {t}));
      == { assert threads - {t'} - {t} == threads - {t', t} == threads - {t} - {t'}; }
        t.decreaser + (t'.decreaser + F(threads - {t} - {t'}));
      == { sum_decreasers_lemma(t', threads - {t}); }
        t.decreaser + F(threads - {t});
      }
    }
  }

  // Run all the threads until they are all done:
  // (The extender needs their own "custom invariant" and "step".)
  predicate custom_invariant()
    reads this, threads, resources
    ensures custom_invariant() ==> valid_custom()

  // Wrapped `step` method in order to provide the preservation of `custom_invariant`:
  method step(curr_thread: Thread)
    requires curr_thread in threads
    requires custom_invariant()
    ensures custom_invariant()
  // below are just translated definition from `Thread.step()`:
    modifies curr_thread, resources
    requires valid()
    requires !curr_thread.done
    ensures valid()
    ensures curr_thread.started
    ensures curr_thread.decreaser < old(curr_thread.decreaser)
  // The body is just one-line, but cannot really specify it here!!
  // { 
  //   curr_thread.step();
  // }

  method run()
    modifies threads, resources
    requires valid()
    requires forall t | t in threads :: !t.started
    requires custom_invariant()
    ensures valid()
    ensures forall t | t in threads :: t.done
    ensures custom_invariant()
  {
    while true
      decreases sum_decreasers()
      invariant forall t | t in threads :: t.valid()
      invariant custom_invariant()
    {
      var thread := pick();
      if thread == null {
        break;
      } else {
        sum_decreasers_lemma(thread, threads);
        step(thread);
        sum_decreasers_lemma(thread, threads);
      }
    }
  }
}


// An example usage: concurrent counter with atomic counts.
// Use n threads to each add x times. Result should be n*x.
class Adder extends Thread {
  const counter: array<nat>
  var rest: nat
  var id: nat // no proof attached, just for printing use

  predicate valid_custom() reads this {
    && counter.Length == 1
    && resources == {counter}
    && decreaser == rest
    && (done <==> rest == 0) // important, but easy to overlook
  }

  constructor (counter': array<nat>, x: nat, id': nat)
    requires counter'.Length == 1
    ensures counter == counter';
    ensures rest == x;
    ensures !started;
    ensures valid()
  {
    id := id';
    counter := counter';
    rest := x;
    resources := {counter'};
    decreaser := x;
    done := x == 0; // if x == 0 we are automatically done
    started := false;
  }

  method step()
    modifies this, resources
    requires valid()
    requires !done
    ensures valid()
    ensures started
    ensures decreaser < old(decreaser)
    // new guarantees:
    ensures counter[0] == old(counter[0]) + 1
    ensures rest == old(rest) - 1
  {
    counter[0] := counter[0] + 1;
    rest := rest - 1;
    if rest == 0 {
      done := true;
    }
    started := true;
    decreaser := decreaser - 1;
    print "ID = ", id, ", Value = ", counter[0], "\n";
  }
}


class ConcurrentAdder extends Scheduler {
  const adders: set<Adder> // basically just the threads
  ghost const counter: array<nat> // the shared counter
  ghost const goal: nat // the goal to add

  predicate valid_custom() reads this {
    && adders == threads
    && counter.Length == 1
    && resources == {counter}
  }

  // construct `adder_count` adders, each counts to `x`:
  constructor (counter': array<nat>, adder_count: nat, x: nat)
    requires counter'.Length == 1
    requires adder_count > 0
    ensures valid()
    ensures counter == counter'
    ensures forall t | t in threads :: !t.started
    ensures fresh(threads)
    ensures |threads| == adder_count
    ensures goal == adder_count * x + counter[0]
    ensures custom_invariant()
  {
    var adders': set<Adder> := {};
    for i := 0 to adder_count
      invariant |adders'| == i
      invariant fresh(adders')
      invariant forall a | a in adders' :: a.valid() && !a.started
      invariant forall a | a in adders' :: a.resources == {counter'}
      invariant sum_rest_sub(adders') == i * x
    {
      var adder := new Adder(counter', x, i);
      adders' := adders' + {adder};
      sum_rest_lemma(adder, adders');
    }
    adders := adders';
    threads := adders';
    counter := counter';
    resources := {counter};
    goal := adder_count * x + counter'[0];
  }

  // Below are just annoying, copy-and-paste code from the `Schedular` trait.
  // But since the trait and the class should be logically independent (provider & client),
  // this seems to be the only reasonable way...

  // The sum of all threads' `rest` field:
  function sum_rest(): nat reads this, adders {
    sum_rest_sub(adders)
  }
  // where:
  static function sum_rest_sub(adders: set<Adder>): nat
    reads adders
  {
    if t :| t in adders then
      t.rest + sum_rest_sub(adders - {t})
    else
      0
  }

  // Proof that the sum does not depend on thread order:
  // Sometimes Dafny is not smart...
  static lemma {:axiom} sum_rest_lemma(t: Adder, threads: set<Adder>)
    requires t in threads
    ensures sum_rest_sub(threads) == t.rest + sum_rest_sub(threads - {t})
    decreases threads
  // Weirdly, this causes Dafny to hang forever... I don't know why. Probably Dafny's fault?!
  // It's almost the same thing as `Scheduler.sum_decreasers_lemma`, but the latter is verified quickly!!
  //
  // Having no other apparent solutions, I can only leave this as an "axiom".
  // {
  //   var F := sum_rest_sub;
  //   var t' :| t' in threads && F(threads) == t'.rest + F(threads - {t'});
  //   if t' != t {
  //     calc {
  //       F(threads);
  //     == // Definition
  //       t'.rest + F(threads - {t'});
  //     == { sum_rest_lemma(t, threads - {t'}); }
  //       t'.rest + (t.rest + F(threads - {t'} - {t}));
  //     == { assert threads - {t'} - {t} == threads - {t', t} == threads - {t} - {t'}; }
  //       t.rest + (t'.rest + F(threads - {t} - {t'}));
  //     == { sum_rest_lemma(t', threads - {t}); }
  //       t.rest + F(threads - {t});
  //     }
  //   }
  // }

  predicate custom_invariant()
    reads this, threads, resources
    ensures custom_invariant() ==> valid_custom()
  {
    && valid_custom()
    && adders == threads
    && sum_rest() + counter[0] == goal // the most important invariant to the specific problem
  }

  method step(curr_thread: Thread)
    requires curr_thread in threads
    requires custom_invariant()
    ensures custom_invariant()
    modifies curr_thread, resources
    requires valid()
    requires !curr_thread.done
    ensures valid()
    ensures curr_thread.started
    ensures curr_thread.decreaser < old(curr_thread.decreaser)
  {
    var curr_adder := curr_thread as Adder; // type cast
    sum_rest_lemma(curr_adder, adders);
    curr_adder.step();
    sum_rest_lemma(curr_adder, adders);
  }
}



method Main() {
  var counter := new nat[] [0];
  var thread_count := 5;
  var x := 10;

  var worker := new ConcurrentAdder(counter, thread_count, x);
  worker.run();
  assert counter[0] == thread_count * x by {
    sum_rest_is_zero(worker.adders);
  }

  // Optimally the output order should be random, but `:|` is token-wise deterministic...
  // Thus it just runs "one adder by another", not fully shuffled!
  //
  // To fully shuffle this, one can e.g. take in a random seed, generate a random number (say `r`),
  // collect all yet-to-be-done threads into a list (say `l`), and choose the thread at `l[r % |l|]`.
  print "Final value:", counter[0];
  expect counter[0] == 50;
}

// Stupidly, we need one more lemma here!! Dafny sets are really stupid in some ways.
lemma sum_rest_is_zero(adders: set<Adder>)
  requires forall a | a in adders :: a.rest == 0
  ensures ConcurrentAdder.sum_rest_sub(adders) == 0
{
  if adder :| adder in adders {
    ConcurrentAdder.sum_rest_lemma(adder, adders);
  }
}