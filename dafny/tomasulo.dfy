module common {
  type pos = i | i > 0 witness 1
  const reg_count: pos
  type reg_index = i | 0 <= i < reg_count witness 0
  const pc_max: nat
  type pc_range = i | 0 <= i <= pc_max witness 0
  type inst_index = i | 0 <= i < pc_max witness *

  type Op
  datatype Instruction =
    | Alu(op: Op, d: reg_index, s1: reg_index, s2: reg_index)  // arbitrary ALU instruction
  function delay_of(op: Op): pos

  type word
  function alu(op: Op, x: word, y: word): word  // uninterpreted calculation

  datatype Taint =
    | InitReg(r: reg_index)   // initial value of register `r`
    | Output(i: inst_index)   // output of instruction `i`
  {
    ghost predicate is_below(pc: pc_range) {
      InitReg? || i < pc
    }
  }
  type TaintPair = (Taint, Taint)

  function arbitrary<T>(): T

  ghost function arbitrary_choice<T(!new)>(P: T -> bool): (x: T)
    requires exists x: T :: P(x)
    ensures P(x)
  {
    var x :| P(x); x
  }
}


module specification {
  import opened common

  datatype State = State(
    reg_file: seq<word>,
    inst_mem: seq<Instruction>,
    pc: pc_range,
    // auxiliary history variables:
    init_regs_: seq<word>,
    outputs_: seq<word>,
    taints_: seq<TaintPair>, // may be shortened to O(|slot_count|)
    last_writer_: seq<Taint>
  ) {
    ghost predicate inv() {  // local invariants:
      && |reg_file| == reg_count
      && |inst_mem| == pc_max
      // for history variables:
      && |init_regs_| == reg_count
      && |outputs_| == pc_max
      && |taints_| == pc_max
      && |last_writer_| == reg_count
      // relations:
      && (forall i | 0 <= i < pc ::
        outputs_[i] == alu(inst_mem[i].op, word_of(taints_[i].0), word_of(taints_[i].1)))
      && (forall i | 0 <= i < pc :: taints_[i].0.is_below(i) && taints_[i].1.is_below(i))
      && (forall i: reg_index :: last_writer_[i].is_below(pc))
      && (forall i: reg_index :: reg_file[i] == word_of(last_writer_[i]))
    }

    ghost function word_of(t: Taint): word
      requires |init_regs_| == reg_count
      requires |outputs_| == pc_max
    {
      match t {
        case InitReg(r) => init_regs_[r]
        case Output(i) => outputs_[i]
      }
    }

    static function init(reg_init: seq<word>, inst_init: seq<Instruction>): (s: State)
      requires |reg_init| == reg_count
      requires |inst_init| == pc_max
      ensures s.inv()
    {
      State(
        reg_file := reg_init,
        inst_mem := inst_init,
        pc := 0,
        // for history variables:
        init_regs_ := reg_init,
        outputs_ := seq(pc_max, _ => arbitrary<word>()),
        taints_ := seq(pc_max, _ => arbitrary<TaintPair>()),
        last_writer_ := seq(reg_count, (i: reg_index) => InitReg(i))
      )
    }

    ghost predicate done() {
      pc == pc_max
    }

    function next(): (s': State)
      requires !done()
      requires inv()
      ensures s'.inv()
    {
      var inst := inst_mem[pc];
      var result := alu(inst.op, reg_file[inst.s1], reg_file[inst.s2]);
      State(
        reg_file := reg_file[inst.d := result],
        pc := pc + 1,
        // update history variables:
        outputs_ := outputs_[pc := result],
        taints_ := taints_[pc := (last_writer_[inst.s1], last_writer_[inst.s2])],
        last_writer_ := last_writer_[inst.d := Output(pc)],
        // unchanged:
        inst_mem := inst_mem, init_regs_ := init_regs_
      )
    }
  }
}


// for simplicity, no pipeline for now:
module tomasulo {
  import opened common
  datatype Reg =
    | WaitingFor(i: inst_index)
    | Word(w: word)

  datatype Slot =  // a slot in reservation station
    | S_Free
    | S_Busy(op: Op, i: inst_index, d: reg_index, r1: Reg, r2: Reg)
  {
    predicate ready() {
      S_Busy? && r1.Word? && r2.Word?
    }
  }

  datatype Result =
    | Empty
    | Result(i: inst_index, d: reg_index, w: word)

  datatype Resource =
    | R_Free
    | R_Busy(result: Result, count_down: nat)

  const slot_count: pos
  type slot_index = i | 0 <= i < slot_count witness 0

  const resource_count: pos
  type resource_index = i | 0 <= i < resource_count witness 0

  datatype Location =  // track location of an instruction
    | NotStarted
    | InSlot(si: slot_index)
    | InResource(ri: resource_index)
    | InResult
    | Finished

  datatype State = State(
    reg_file: seq<Reg>,
    inst_mem: seq<Instruction>,
    pc: pc_range,
    // out-of-order facilities:
    slots: seq<Slot>,
    resources: seq<Resource>,
    result: Result,
    // auxiliary history variables:
    init_regs_: seq<word>,
    outputs_: seq<Reg>,
    taints_: seq<TaintPair>,
    last_writer_: seq<Taint>,
    locations_: seq<Location>
  ) {
    ghost predicate inv() {  // local invariants:
      && valid_lengths()
      && (forall i: slot_index :: slots[i].S_Busy? ==> valid_slot(i))
      && (forall i: resource_index :: resources[i].R_Busy? ==> valid_resource(i))
      && (result.Result? ==> valid_result(result))
      && (forall i | 0 <= i < pc :: outputs_[i].Word? ==> valid_output(i))
      && (forall i | 0 <= i < pc :: valid_location(i))
      && (forall i | 0 <= i < pc :: taints_[i].0.is_below(i) && taints_[i].1.is_below(i))
      && (forall i: reg_index :: valid_last_writer(i))
      && (forall i: reg_index :: reg_file[i] == word_of(last_writer_[i]))
      && (forall i: inst_index, j: reg_index :: valid_reg_waiting(i, j))
      && (forall i: inst_index, j: slot_index :: slots[j].S_Busy? ==> valid_slot_waiting(i, j))
    }

    ghost predicate valid_lengths() {
      && |reg_file| == reg_count
      && |inst_mem| == pc_max
      && |slots| == slot_count
      && |resources| == resource_count
      // for history variables:
      && |init_regs_| == reg_count
      && |outputs_| == pc_max
      && |taints_| == pc_max
      && |last_writer_| == reg_count
      && |locations_| == pc_max
    }

    ghost predicate valid_slot(i: slot_index)
      requires valid_lengths()
      requires slots[i].S_Busy?
    {
      var pc' := slots[i].i;
      var inst, taint := inst_mem[pc'], taints_[pc'];
      var s1, s2 := word_of(taint.0), word_of(taint.1);
      && pc' < pc && slots[i] == S_Busy(inst.op, pc', inst.d, s1, s2)
    }

    ghost predicate valid_resource(i: resource_index)
      requires valid_lengths()
      requires resources[i].R_Busy?
    {
      resources[i].result.Result? && valid_result(resources[i].result)
    }

    ghost predicate valid_result(res: Result)
      requires valid_lengths()
      requires res.Result?
    {
      var pc' := res.i;
      var inst, taint := inst_mem[pc'], taints_[pc'];
      var s1, s2 := word_of(taint.0), word_of(taint.1);
      pc' < pc && s1.Word? && s2.Word? && res == Result(pc', inst.d, alu(inst.op, s1.w, s2.w))
    }

    ghost predicate valid_output(i: inst_index)
      requires valid_lengths()
      requires outputs_[i].Word?
    {
      var s1, s2 := word_of(taints_[i].0), word_of(taints_[i].1);
      s1.Word? && s2.Word? && outputs_[i].w == alu(inst_mem[i].op, s1.w, s2.w)
    }

    ghost function word_of(t: Taint): Reg
      requires |init_regs_| == reg_count
      requires |outputs_| == pc_max
    {
      match t {
        case InitReg(r) => Word(init_regs_[r])
        case Output(i) => outputs_[i]
      }
    }

    ghost predicate valid_location(i: inst_index)
      requires valid_lengths()
    {
      && (locations_[i] == NotStarted <==> i >= pc)
      && (forall si: slot_index :: locations_[i] == InSlot(si) <==> in_slot(i, si))
      && (forall ri: resource_index :: locations_[i] == InResource(ri) <==> in_resource(i, ri))
      && (locations_[i] == InResult <==> in_result(i))
      && (locations_[i] == Finished <==> finished(i))
    }
    ghost predicate in_slot(i: inst_index, si: slot_index) requires valid_lengths() {
      slots[si].S_Busy? && slots[si].i == i
    }
    ghost predicate in_resource(i: inst_index, ri: resource_index) requires valid_lengths() {
      resources[ri].R_Busy? && resources[ri].result.Result? && resources[ri].result.i == i
    }
    ghost predicate in_result(i: inst_index) requires valid_lengths() {
      result.Result? && result.i == i
    }
    ghost predicate finished(i: inst_index) requires valid_lengths() {
      outputs_[i].Word?
    }

    ghost predicate valid_last_writer(i: reg_index)
      requires valid_lengths()
    {
      && last_writer_[i].is_below(pc)
      && (last_writer_[i].Output? ==> inst_mem[last_writer_[i].i].d == i)
    }

    ghost predicate valid_reg_waiting(i: inst_index, j: reg_index)
      requires valid_lengths()
    {
      && (reg_file[j] == WaitingFor(i) ==> last_writer_[j] == Output(i))
    }

    ghost predicate valid_slot_waiting(i: inst_index, j: slot_index)
      requires valid_lengths()
      requires slots[j].S_Busy?
    {
      && (slots[j].r1 == WaitingFor(i) ==> taints_[slots[j].i].0 == Output(i))
      && (slots[j].r2 == WaitingFor(i) ==> taints_[slots[j].i].1 == Output(i))
    }

    ghost predicate done() requires inv() {
      && pc == pc_max
      && (forall i: slot_index :: slots[i].S_Free?)
      && (forall i: resource_index :: resources[i].R_Free?)
      && result.Empty?
    }

    static function init(reg_init: seq<word>, inst_init: seq<Instruction>): (s: State)
      requires |reg_init| == reg_count
      requires |inst_init| == pc_max
      ensures s.inv()
    {
      State(
        reg_file := seq(reg_count, (i: reg_index) => Word(reg_init[i])),
        inst_mem := inst_init,
        pc := 0,
        slots := seq(slot_count, _ => S_Free),
        resources := seq(resource_count, _ => R_Free),
        result := Empty,
        // for history variables:
        init_regs_ := reg_init,
        outputs_ := seq(pc_max, _ => arbitrary<Reg>()),
        taints_ := seq(pc_max, _ => arbitrary<TaintPair>()),
        last_writer_ := seq(reg_count, (i: reg_index) => InitReg(i)),
        locations_ := seq(pc_max, _ => NotStarted)
      )
    }

    // dispatch an inst from inst_mem to a free slot:
    predicate can_dispatch(i: slot_index) requires inv() {
      && pc < pc_max
      && slots[i].S_Free?
    }
    function dispatch(i: slot_index): (s': State) requires inv()
      requires can_dispatch(i)
    {
      var inst := inst_mem[pc];
      var slot_item := S_Busy(inst.op, pc, inst.d, reg_file[inst.s1], reg_file[inst.s2]);
      State(
        reg_file := reg_file[inst.d := WaitingFor(pc)],
        slots := slots[i := slot_item],
        pc := pc + 1,
        // update history variables:
        outputs_ := outputs_[pc := WaitingFor(pc)],
        taints_ := taints_[pc := (last_writer_[inst.s1], last_writer_[inst.s2])],
        last_writer_ := last_writer_[inst.d := Output(pc)],
        locations_ := locations_[pc := InSlot(i)],
        // unchanged:
        inst_mem := inst_mem, resources := resources, result := result,
        init_regs_ := init_regs_
      )
    }
    lemma dispatch_preserves_inv(i_: slot_index, s': State) requires inv()
      requires can_dispatch(i_) && s' == dispatch(i_)
      ensures s'.inv()
    {
      forall i: slot_index | s'.slots[i].S_Busy? ensures s'.valid_slot(i) {
        if i == i_ {
          var inst, taint := s'.inst_mem[pc], s'.taints_[pc];
          var s1, s2 := s'.word_of(taint.0), s'.word_of(taint.1);
          assert s'.slots[i].r1 == s1 by {
            assert reg_file[inst.s1] == word_of(last_writer_[inst.s1]);
            assert valid_last_writer(inst.s1);
          }
          assert s'.slots[i].r2 == s2 by {
            assert reg_file[inst.s2] == word_of(last_writer_[inst.s2]);
            assert valid_last_writer(inst.s2);
          }
        }
      }
      forall i: resource_index | s'.resources[i].R_Busy? ensures s'.valid_resource(i) {
        // automatic
      }
      forall i | 0 <= i < s'.pc && s'.outputs_[i].Word? ensures s'.valid_output(i) {
        // automatic
      }
      forall i | 0 <= i < s'.pc ensures s'.valid_location(i) {
        if i == pc {
          assert s'.in_slot(i, i_);
        } else {
          assert valid_location(i);
        }
      }
      forall i | 0 <= i < s'.pc ensures s'.taints_[i].0.is_below(i) && s'.taints_[i].1.is_below(i) {
        if i == pc {
          var inst := s'.inst_mem[pc];
          assert valid_last_writer(inst.s1) && valid_last_writer(inst.s2);
        }
      }
      forall i: reg_index ensures s'.valid_last_writer(i) {
        assert valid_last_writer(i);
      }
      forall i: reg_index ensures s'.reg_file[i] == s'.word_of(s'.last_writer_[i]) {
        assert valid_last_writer(i);
      }
      forall i: inst_index, j: reg_index ensures s'.valid_reg_waiting(i, j) {
        assert valid_reg_waiting(i, j);
      }
      forall i: inst_index, j: slot_index | s'.slots[j].S_Busy? ensures s'.valid_slot_waiting(i, j) {
        if j == i_ {
          var inst := s'.inst_mem[pc];
          if s'.slots[j].r1 == WaitingFor(i) {
            assert valid_reg_waiting(i, inst.s1);
          }
          if s'.slots[j].r2 == WaitingFor(i) {
            assert valid_reg_waiting(i, inst.s2);
          }
        } else {
          assert valid_slot_waiting(i, j);
        }
      }
    }

    // when a slot is ready, start executing it:
    predicate can_start_exec(i: slot_index, j: resource_index) requires inv() {
      && slots[i].ready()
      && resources[j].R_Free?
    }
    function start_exec(i: slot_index, j: resource_index): (s': State) requires inv()
      requires can_start_exec(i, j)
    {
      var resource_item := R_Busy(
        result := Result(slots[i].i, slots[i].d, alu(slots[i].op, slots[i].r1.w, slots[i].r2.w)),
        count_down := delay_of(slots[i].op)
      );
      State(
        slots := slots[i := S_Free],
        resources := resources[j := resource_item],
        // update history variables:
        locations_ := locations_[slots[i].i := InResource(j)],
        // unchanged:
        reg_file := reg_file, inst_mem := inst_mem, pc := pc, result := result,
        init_regs_ := init_regs_, outputs_ := outputs_, taints_ := taints_, last_writer_ := last_writer_
      )
    }
    lemma start_exec_preserves_inv(i_: slot_index, j: resource_index, s': State) requires inv()
      requires can_start_exec(i_, j) && s' == start_exec(i_, j)
      ensures s'.inv()
    {
      forall i: slot_index | s'.slots[i].S_Busy? ensures s'.valid_slot(i) {
        // automatic 
      }
      forall i: resource_index | s'.resources[i].R_Busy? ensures s'.valid_resource(i) {
        // automatic
      }
      forall i | 0 <= i < s'.pc && s'.outputs_[i].Word? ensures s'.valid_output(i) {
        // automatic
      }
      forall i | 0 <= i < s'.pc ensures s'.valid_location(i) {
        assert valid_location(i);
        if i == slots[i_].i {
          assert in_slot(i, i_);
        }
      }
      forall i | 0 <= i < s'.pc ensures s'.taints_[i].0.is_below(i) && s'.taints_[i].1.is_below(i) {
        // automatic
      }
      forall i: reg_index ensures s'.valid_last_writer(i) {
        assert valid_last_writer(i);
      }
      forall i: reg_index ensures s'.reg_file[i] == s'.word_of(s'.last_writer_[i]) {
        // automatic
      }
      forall i: inst_index, j: reg_index ensures s'.valid_reg_waiting(i, j) {
        assert valid_reg_waiting(i, j);
      }
      forall i: inst_index, j: slot_index | s'.slots[j].S_Busy? ensures s'.valid_slot_waiting(i, j) {
        assert valid_slot_waiting(i, j);
      }
    }

    // execute one cycle for a multi-cycle operation:
    predicate can_exec(j: resource_index) requires inv() {
      && resources[j].R_Busy?
      && resources[j].count_down > 0
    }
    function exec(j: resource_index): (s': State) requires inv()
      requires can_exec(j)
    {
      State(
        resources := resources[j := R_Busy(resources[j].result, resources[j].count_down - 1)],
        // unchanged:
        reg_file := reg_file, inst_mem := inst_mem, pc := pc, slots := slots, result := result,
        init_regs_ := init_regs_, outputs_ := outputs_, taints_ := taints_,
        last_writer_ := last_writer_, locations_ := locations_
      )
    }
    lemma exec_preserves_inv(j: resource_index, s': State) requires inv()
      requires can_exec(j) && s' == exec(j)
      ensures s'.inv()
    {
      forall i: slot_index | s'.slots[i].S_Busy? ensures s'.valid_slot(i) {
        // automatic
      }
      forall i: resource_index | s'.resources[i].R_Busy? ensures s'.valid_resource(i) {
        // automatic
      }
      forall i | 0 <= i < s'.pc && s'.outputs_[i].Word? ensures s'.valid_output(i) {
        // automatic
      }
      forall i | 0 <= i < s'.pc ensures s'.valid_location(i) {
        assert valid_location(i);
      }
      forall i | 0 <= i < s'.pc ensures s'.taints_[i].0.is_below(i) && s'.taints_[i].1.is_below(i) {
        // automatic
      }
      forall i: reg_index ensures s'.valid_last_writer(i) {
        assert valid_last_writer(i);
      }
      forall i: reg_index ensures s'.reg_file[i] == s'.word_of(s'.last_writer_[i]) {
        // automatic
      }
      forall i: inst_index, j: reg_index ensures s'.valid_reg_waiting(i, j) {
        assert valid_reg_waiting(i, j);
      }
      forall i: inst_index, j: slot_index | s'.slots[j].S_Busy? ensures s'.valid_slot_waiting(i, j) {
        assert valid_slot_waiting(i, j);
      }
    }

    // copy the result from a finished operation:
    predicate can_finish_exec(j: resource_index) requires inv() {
      && resources[j].R_Busy?
      && resources[j].count_down == 0
      && result.Empty?
    }
    function finish_exec(j: resource_index): (s': State) requires inv()
      requires can_finish_exec(j)
    {
      State(
        result := resources[j].result,
        resources := resources[j := R_Free],
        // update history variables:
        locations_ := locations_[resources[j].result.i := InResult],
        // unchanged:
        reg_file := reg_file, inst_mem := inst_mem, pc := pc, slots := slots,
        init_regs_ := init_regs_, outputs_ := outputs_, taints_ := taints_, last_writer_ := last_writer_
      )
    }
    lemma finish_exec_preserves_inv(j: resource_index, s': State) requires inv()
      requires can_finish_exec(j) && s' == finish_exec(j)
      ensures s'.inv()
    {
      forall i: slot_index | s'.slots[i].S_Busy? ensures s'.valid_slot(i) {
        // automatic
      }
      forall i: resource_index | s'.resources[i].R_Busy? ensures s'.valid_resource(i) {
        // automatic
      }
      forall i | 0 <= i < s'.pc && s'.outputs_[i].Word? ensures s'.valid_output(i) {
        // automatic
      }
      forall i | 0 <= i < s'.pc ensures s'.valid_location(i) {
        assert valid_location(i);
        if i == resources[j].result.i {
          assert in_resource(i, j);
        }
      }
      forall i | 0 <= i < s'.pc ensures s'.taints_[i].0.is_below(i) && s'.taints_[i].1.is_below(i) {
        // automatic
      }
      forall i: reg_index ensures s'.valid_last_writer(i) {
        assert valid_last_writer(i);
      }
      forall i: reg_index ensures s'.reg_file[i] == s'.word_of(s'.last_writer_[i]) {
        // automatic
      }
      forall i: inst_index, j: reg_index ensures s'.valid_reg_waiting(i, j) {
        assert valid_reg_waiting(i, j);
      }
      forall i: inst_index, j: slot_index | s'.slots[j].S_Busy? ensures s'.valid_slot_waiting(i, j) {
        assert valid_slot_waiting(i, j);
      }
    }

    // broadcast the result to the reg_file and the reserved slots:
    predicate can_broadcast_result() requires inv() {
      && result.Result?
    }
    function broadcast_result(): (s': State) requires inv()
      requires can_broadcast_result()
    {
      State(
        reg_file :=
          if reg_file[result.d] == WaitingFor(result.i) then reg_file[result.d := Word(result.w)]
          else reg_file,
        slots := seq(slot_count, (i: slot_index) =>
          if slots[i].S_Free? then S_Free
          else S_Busy(
            r1 := if slots[i].r1 == WaitingFor(result.i) then Word(result.w) else slots[i].r1,
            r2 := if slots[i].r2 == WaitingFor(result.i) then Word(result.w) else slots[i].r2,
            /* unchanged: */ op := slots[i].op, i := slots[i].i, d := slots[i].d)),
        result := Empty,
        // update history variables:
        outputs_ := outputs_[result.i := Word(result.w)],
        locations_ := locations_[result.i := Finished],
        // unchanged:
        inst_mem := inst_mem, pc := pc, resources := resources,
        init_regs_ := init_regs_, taints_ := taints_, last_writer_ := last_writer_
      )
    }
    lemma broadcast_result_preserves_inv(s': State) requires inv()
      requires can_broadcast_result() && s' == broadcast_result()
      ensures s'.inv()
    {
      forall i: slot_index | s'.slots[i].S_Busy? ensures s'.valid_slot(i) {
        var pc' := s'.slots[i].i;
        var inst, taint := s'.inst_mem[pc'], s'.taints_[pc'];
        var s1, s2 := s'.word_of(taint.0), s'.word_of(taint.1);

        assert s'.slots[i].r1 == s1 by {
          if slots[i].r1.WaitingFor? {
            assert valid_slot_waiting(slots[i].r1.i, i);
          } else if taint.0.Output? {
            assert valid_location(taint.0.i);
          }
        }
        assert s'.slots[i].r2 == s2 by {
          if slots[i].r2.WaitingFor? {
            assert valid_slot_waiting(slots[i].r2.i, i);
          } else if taint.1.Output? {
            assert valid_location(taint.1.i);
          }
        }
      }
      forall i: resource_index | s'.resources[i].R_Busy? ensures s'.valid_resource(i) {
        // automatic
      }
      forall i | 0 <= i < s'.pc && s'.outputs_[i].Word? ensures s'.valid_output(i) {
        // automatic
      }
      forall i | 0 <= i < s'.pc ensures s'.valid_location(i) { 
        assert valid_location(i);
      }
      forall i | 0 <= i < s'.pc ensures s'.taints_[i].0.is_below(i) && s'.taints_[i].1.is_below(i) {
        // automatic
      }
      forall i: reg_index ensures s'.valid_last_writer(i) {
        assert valid_last_writer(i);
      }
      forall i: reg_index ensures s'.reg_file[i] == s'.word_of(s'.last_writer_[i]) {
        if i == result.d {
          if reg_file[i].WaitingFor? {
            assert valid_reg_waiting(reg_file[i].i, i);
          }
        } else {
          assert valid_last_writer(i);
        }
      }
      forall i: inst_index, j: reg_index ensures s'.valid_reg_waiting(i, j) {
        assert valid_reg_waiting(i, j);
      }
      forall i: inst_index, j: slot_index | s'.slots[j].S_Busy? ensures s'.valid_slot_waiting(i, j) {
        assert valid_slot_waiting(i, j);
      }
    }

    // non-deterministically decide one atomic step:
    ghost function guards(): seq<bool> requires inv() {[
      exists i :: can_dispatch(i),
      exists i, j :: can_start_exec(i, j),
      exists j :: can_exec(j),
      exists j :: can_finish_exec(j),
      can_broadcast_result()
    ]}
    ghost predicate can_choose(i: int) requires inv() {
      0 <= i < |guards()| && guards()[i]
    }
    ghost function next(): (s': State) requires inv() ensures s'.inv()
      requires !done()
    {
      action_exists();
      var choice := arbitrary_choice<int>(can_choose);
      match choice {
        case 0 => var i :| can_dispatch(i); dispatch_preserves_inv(i, dispatch(i));
          dispatch(i)
        case 1 => var i, j :| can_start_exec(i, j); start_exec_preserves_inv(i, j, start_exec(i, j));
          start_exec(i, j)
        case 2 => var j :| can_exec(j); exec_preserves_inv(j, exec(j));
          exec(j)
        case 3 => var j :| can_finish_exec(j); finish_exec_preserves_inv(j, finish_exec(j));
          finish_exec(j)
        case 4 => broadcast_result_preserves_inv(broadcast_result());
          broadcast_result()
      }
    }

    lemma action_exists() requires inv() requires !done()
      ensures exists i :: can_choose(i)
    {
      if result.Result? {
        assert can_broadcast_result() && can_choose(4);
      } else if ri: resource_index :| resources[ri].R_Busy? {
        if resources[ri].count_down == 0 {
          assert can_finish_exec(ri) && can_choose(3);
        } else {
          assert can_exec(ri) && can_choose(2);
        }
      } else if si: slot_index :| slots[si].S_Busy? {
        var sj := si;
        while !slots[sj].ready()
          invariant slots[sj].S_Busy?
          decreases slots[sj].i
        {
          var i := slots[si].i;
          var i' := if slots[sj].r1.WaitingFor? then slots[sj].r1.i else slots[sj].r2.i;
          assert i' < i by {
            assert valid_slot_waiting(i', sj);
          }
          assert valid_location(i');
          assert locations_[i'].InSlot?;
          sj := locations_[i'].si;
        }
        assert can_start_exec(sj, 0) && can_choose(1);
      } else {
        assert can_dispatch(0) && can_choose(0);
      }
    }
  }
}
