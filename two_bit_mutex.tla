(* Copyright (C) 2022 Malte Skarupke

   This is free software; you can redistribute it and/or
   modify it under the terms of the GNU Lesser General Public
   License as published by the Free Software Foundation; either
   version 2.1 of the License, or (at your option) any later version.

   See https://www.gnu.org/licenses/.  *)

-------------------------- MODULE two_bit_mutex --------------------------

EXTENDS Integers, FiniteSets, Sequences
CONSTANT Procs

Bit(i) == 2 ^ i
ClearBit(i, b) == (i % Bit(b)) + (i \div Bit(b+1)) * Bit(b+1)
SetBit(i, b) == ClearBit(i, b) + Bit(b)
Xor1(i) == IF (i % 2) = 0 THEN i + 1 ELSE i - 1
LockedBit == Bit(0)
SleeperBit == Bit(1)

AllProcs == Procs

(*
--algorithm lll_mutex_and_cv
{
variables 
  mutex_index = 0;
  futexes = [i \in {mutex_index} |-> [state |-> 0, sleepers |-> {}]];
  
procedure futex_wait(wait_index = 0, val = 0)
{
  check_state:
    if (futexes[wait_index].state /= val)
    {
        return;
    }
    else
    {
        val := 0;
        futexes[wait_index].sleepers := futexes[wait_index].sleepers \union {self};
      wait_for_wake:
        await ~ (self \in futexes[wait_index].sleepers);
        return;
    };
}
procedure futex_wake_single(wake_index = 0)
{
  check_for_sleepers:
    if (futexes[wake_index].sleepers = {})
    {
        return;
    }
    else
    {
        with (x \in futexes[wake_index].sleepers)
        {
            futexes[wake_index].sleepers := futexes[wake_index].sleepers \ {x};
        };
        return;
    };
}

procedure futex_wake_all(wake_all_index = 0)
{
  futex_wake_all:
    futexes[wake_all_index].sleepers := {};
    return;
}

procedure set(value)
variable old_state = 0;
{
set_start:
  old_state := futexes[mutex_index].state;
set_compare_exchange:
  if (futexes[mutex_index].state = old_state)
  {
    futexes[mutex_index].state := value + (old_state % 4);
    return;
  }
  else
  {
    old_state := futexes[mutex_index].state;
    goto set_compare_exchange;
  };
}

procedure lock()
variable old_state = 0;
{
lock_start:
  old_state := futexes[mutex_index].state;
lock_compare_exchange:
  if ((old_state % 4) = 0 /\ futexes[mutex_index].state = old_state)
  {
    futexes[mutex_index].state := old_state + LockedBit;
    return;
  };
lock_loop:
  while (TRUE)
  {
    if (old_state % 4 > LockedBit)
    {
      call futex_wait(mutex_index, old_state);
    lock_reload_1:
      old_state := futexes[mutex_index].state;
    }
    else if (futexes[mutex_index].state = old_state)
    {
      futexes[mutex_index].state := old_state + SleeperBit;
    lock_after_exchange:
      if ((old_state % 4) = 0)
      {
        return;
      }
      else
      {
        call futex_wait(mutex_index, old_state + SleeperBit);
      lock_reload_2:
        old_state := futexes[mutex_index].state;
      }
    }
    else
    {
      old_state := futexes[mutex_index].state;
    };
  };
};

procedure unlock ()
variable old_state = 0;
{
unlock_start:
  old_state := futexes[mutex_index].state;
  futexes[mutex_index].state := futexes[mutex_index].state - (futexes[mutex_index].state % 4);
unlock_maybe_wake:
  if (old_state % 4 > 1)
  {
    call futex_wake_single(mutex_index);
    return;
  }
  else return;
}

fair process (Proc \in Procs)
{
proc_start:
  call lock();
cs:
  call unlock();
maybe_loop:
  either
  {
    goto proc_start;
  }
  or
  {
    goto proc_done;
  };
proc_done:
  skip;
}
fair process (Setter \in {1})
{
set_4:
  call set(4);
check_4:
  await (futexes[mutex_index].state - (futexes[mutex_index].state % 4)) = 4;
set_8:
  call set(8);
check_8:
  await (futexes[mutex_index].state - (futexes[mutex_index].state % 4)) = 8;
\*set_12:
\*  call set(12);
\*check_12:
\*  await (futexes[mutex_index].state - (futexes[mutex_index].state % 4)) = 12;
\*set_16:
\*  call set(16);
\*check_16:
\*  await (futexes[mutex_index].state - (futexes[mutex_index].state % 4)) = 16;
}
}
*)

\* BEGIN TRANSLATION (chksum(pcal) = "79546b34" /\ chksum(tla) = "6619b0fd")
\* Label futex_wake_all of procedure futex_wake_all at line 67 col 5 changed to futex_wake_all_
\* Procedure variable old_state of procedure set at line 72 col 10 changed to old_state_
\* Procedure variable old_state of procedure lock at line 90 col 10 changed to old_state_l
CONSTANT defaultInitValue
VARIABLES mutex_index, futexes, pc, stack, wait_index, val, wake_index, 
          wake_all_index, value, old_state_, old_state_l, old_state

vars == << mutex_index, futexes, pc, stack, wait_index, val, wake_index, 
           wake_all_index, value, old_state_, old_state_l, old_state >>

ProcSet == (Procs) \cup ({1})

Init == (* Global variables *)
        /\ mutex_index = 0
        /\ futexes = [i \in {mutex_index} |-> [state |-> 0, sleepers |-> {}]]
        (* Procedure futex_wait *)
        /\ wait_index = [ self \in ProcSet |-> 0]
        /\ val = [ self \in ProcSet |-> 0]
        (* Procedure futex_wake_single *)
        /\ wake_index = [ self \in ProcSet |-> 0]
        (* Procedure futex_wake_all *)
        /\ wake_all_index = [ self \in ProcSet |-> 0]
        (* Procedure set *)
        /\ value = [ self \in ProcSet |-> defaultInitValue]
        /\ old_state_ = [ self \in ProcSet |-> 0]
        (* Procedure lock *)
        /\ old_state_l = [ self \in ProcSet |-> 0]
        (* Procedure unlock *)
        /\ old_state = [ self \in ProcSet |-> 0]
        /\ stack = [self \in ProcSet |-> << >>]
        /\ pc = [self \in ProcSet |-> CASE self \in Procs -> "proc_start"
                                        [] self \in {1} -> "set_4"]

check_state(self) == /\ pc[self] = "check_state"
                     /\ IF futexes[wait_index[self]].state /= val[self]
                           THEN /\ pc' = [pc EXCEPT ![self] = Head(stack[self]).pc]
                                /\ wait_index' = [wait_index EXCEPT ![self] = Head(stack[self]).wait_index]
                                /\ val' = [val EXCEPT ![self] = Head(stack[self]).val]
                                /\ stack' = [stack EXCEPT ![self] = Tail(stack[self])]
                                /\ UNCHANGED futexes
                           ELSE /\ val' = [val EXCEPT ![self] = 0]
                                /\ futexes' = [futexes EXCEPT ![wait_index[self]].sleepers = futexes[wait_index[self]].sleepers \union {self}]
                                /\ pc' = [pc EXCEPT ![self] = "wait_for_wake"]
                                /\ UNCHANGED << stack, wait_index >>
                     /\ UNCHANGED << mutex_index, wake_index, wake_all_index, 
                                     value, old_state_, old_state_l, old_state >>

wait_for_wake(self) == /\ pc[self] = "wait_for_wake"
                       /\ ~ (self \in futexes[wait_index[self]].sleepers)
                       /\ pc' = [pc EXCEPT ![self] = Head(stack[self]).pc]
                       /\ wait_index' = [wait_index EXCEPT ![self] = Head(stack[self]).wait_index]
                       /\ val' = [val EXCEPT ![self] = Head(stack[self]).val]
                       /\ stack' = [stack EXCEPT ![self] = Tail(stack[self])]
                       /\ UNCHANGED << mutex_index, futexes, wake_index, 
                                       wake_all_index, value, old_state_, 
                                       old_state_l, old_state >>

futex_wait(self) == check_state(self) \/ wait_for_wake(self)

check_for_sleepers(self) == /\ pc[self] = "check_for_sleepers"
                            /\ IF futexes[wake_index[self]].sleepers = {}
                                  THEN /\ pc' = [pc EXCEPT ![self] = Head(stack[self]).pc]
                                       /\ wake_index' = [wake_index EXCEPT ![self] = Head(stack[self]).wake_index]
                                       /\ stack' = [stack EXCEPT ![self] = Tail(stack[self])]
                                       /\ UNCHANGED futexes
                                  ELSE /\ \E x \in futexes[wake_index[self]].sleepers:
                                            futexes' = [futexes EXCEPT ![wake_index[self]].sleepers = futexes[wake_index[self]].sleepers \ {x}]
                                       /\ pc' = [pc EXCEPT ![self] = Head(stack[self]).pc]
                                       /\ wake_index' = [wake_index EXCEPT ![self] = Head(stack[self]).wake_index]
                                       /\ stack' = [stack EXCEPT ![self] = Tail(stack[self])]
                            /\ UNCHANGED << mutex_index, wait_index, val, 
                                            wake_all_index, value, old_state_, 
                                            old_state_l, old_state >>

futex_wake_single(self) == check_for_sleepers(self)

futex_wake_all_(self) == /\ pc[self] = "futex_wake_all_"
                         /\ futexes' = [futexes EXCEPT ![wake_all_index[self]].sleepers = {}]
                         /\ pc' = [pc EXCEPT ![self] = Head(stack[self]).pc]
                         /\ wake_all_index' = [wake_all_index EXCEPT ![self] = Head(stack[self]).wake_all_index]
                         /\ stack' = [stack EXCEPT ![self] = Tail(stack[self])]
                         /\ UNCHANGED << mutex_index, wait_index, val, 
                                         wake_index, value, old_state_, 
                                         old_state_l, old_state >>

futex_wake_all(self) == futex_wake_all_(self)

set_start(self) == /\ pc[self] = "set_start"
                   /\ old_state_' = [old_state_ EXCEPT ![self] = futexes[mutex_index].state]
                   /\ pc' = [pc EXCEPT ![self] = "set_compare_exchange"]
                   /\ UNCHANGED << mutex_index, futexes, stack, wait_index, 
                                   val, wake_index, wake_all_index, value, 
                                   old_state_l, old_state >>

set_compare_exchange(self) == /\ pc[self] = "set_compare_exchange"
                              /\ IF futexes[mutex_index].state = old_state_[self]
                                    THEN /\ futexes' = [futexes EXCEPT ![mutex_index].state = value[self] + (old_state_[self] % 4)]
                                         /\ pc' = [pc EXCEPT ![self] = Head(stack[self]).pc]
                                         /\ old_state_' = [old_state_ EXCEPT ![self] = Head(stack[self]).old_state_]
                                         /\ value' = [value EXCEPT ![self] = Head(stack[self]).value]
                                         /\ stack' = [stack EXCEPT ![self] = Tail(stack[self])]
                                    ELSE /\ old_state_' = [old_state_ EXCEPT ![self] = futexes[mutex_index].state]
                                         /\ pc' = [pc EXCEPT ![self] = "set_compare_exchange"]
                                         /\ UNCHANGED << futexes, stack, value >>
                              /\ UNCHANGED << mutex_index, wait_index, val, 
                                              wake_index, wake_all_index, 
                                              old_state_l, old_state >>

set(self) == set_start(self) \/ set_compare_exchange(self)

lock_start(self) == /\ pc[self] = "lock_start"
                    /\ old_state_l' = [old_state_l EXCEPT ![self] = futexes[mutex_index].state]
                    /\ pc' = [pc EXCEPT ![self] = "lock_compare_exchange"]
                    /\ UNCHANGED << mutex_index, futexes, stack, wait_index, 
                                    val, wake_index, wake_all_index, value, 
                                    old_state_, old_state >>

lock_compare_exchange(self) == /\ pc[self] = "lock_compare_exchange"
                               /\ IF (old_state_l[self] % 4) = 0 /\ futexes[mutex_index].state = old_state_l[self]
                                     THEN /\ futexes' = [futexes EXCEPT ![mutex_index].state = old_state_l[self] + LockedBit]
                                          /\ pc' = [pc EXCEPT ![self] = Head(stack[self]).pc]
                                          /\ old_state_l' = [old_state_l EXCEPT ![self] = Head(stack[self]).old_state_l]
                                          /\ stack' = [stack EXCEPT ![self] = Tail(stack[self])]
                                     ELSE /\ pc' = [pc EXCEPT ![self] = "lock_loop"]
                                          /\ UNCHANGED << futexes, stack, 
                                                          old_state_l >>
                               /\ UNCHANGED << mutex_index, wait_index, val, 
                                               wake_index, wake_all_index, 
                                               value, old_state_, old_state >>

lock_loop(self) == /\ pc[self] = "lock_loop"
                   /\ IF old_state_l[self] % 4 > LockedBit
                         THEN /\ /\ stack' = [stack EXCEPT ![self] = << [ procedure |->  "futex_wait",
                                                                          pc        |->  "lock_reload_1",
                                                                          wait_index |->  wait_index[self],
                                                                          val       |->  val[self] ] >>
                                                                      \o stack[self]]
                                 /\ val' = [val EXCEPT ![self] = old_state_l[self]]
                                 /\ wait_index' = [wait_index EXCEPT ![self] = mutex_index]
                              /\ pc' = [pc EXCEPT ![self] = "check_state"]
                              /\ UNCHANGED << futexes, old_state_l >>
                         ELSE /\ IF futexes[mutex_index].state = old_state_l[self]
                                    THEN /\ futexes' = [futexes EXCEPT ![mutex_index].state = old_state_l[self] + SleeperBit]
                                         /\ pc' = [pc EXCEPT ![self] = "lock_after_exchange"]
                                         /\ UNCHANGED old_state_l
                                    ELSE /\ old_state_l' = [old_state_l EXCEPT ![self] = futexes[mutex_index].state]
                                         /\ pc' = [pc EXCEPT ![self] = "lock_loop"]
                                         /\ UNCHANGED futexes
                              /\ UNCHANGED << stack, wait_index, val >>
                   /\ UNCHANGED << mutex_index, wake_index, wake_all_index, 
                                   value, old_state_, old_state >>

lock_reload_1(self) == /\ pc[self] = "lock_reload_1"
                       /\ old_state_l' = [old_state_l EXCEPT ![self] = futexes[mutex_index].state]
                       /\ pc' = [pc EXCEPT ![self] = "lock_loop"]
                       /\ UNCHANGED << mutex_index, futexes, stack, wait_index, 
                                       val, wake_index, wake_all_index, value, 
                                       old_state_, old_state >>

lock_after_exchange(self) == /\ pc[self] = "lock_after_exchange"
                             /\ IF (old_state_l[self] % 4) = 0
                                   THEN /\ pc' = [pc EXCEPT ![self] = Head(stack[self]).pc]
                                        /\ old_state_l' = [old_state_l EXCEPT ![self] = Head(stack[self]).old_state_l]
                                        /\ stack' = [stack EXCEPT ![self] = Tail(stack[self])]
                                        /\ UNCHANGED << wait_index, val >>
                                   ELSE /\ /\ stack' = [stack EXCEPT ![self] = << [ procedure |->  "futex_wait",
                                                                                    pc        |->  "lock_reload_2",
                                                                                    wait_index |->  wait_index[self],
                                                                                    val       |->  val[self] ] >>
                                                                                \o stack[self]]
                                           /\ val' = [val EXCEPT ![self] = old_state_l[self] + SleeperBit]
                                           /\ wait_index' = [wait_index EXCEPT ![self] = mutex_index]
                                        /\ pc' = [pc EXCEPT ![self] = "check_state"]
                                        /\ UNCHANGED old_state_l
                             /\ UNCHANGED << mutex_index, futexes, wake_index, 
                                             wake_all_index, value, old_state_, 
                                             old_state >>

lock_reload_2(self) == /\ pc[self] = "lock_reload_2"
                       /\ old_state_l' = [old_state_l EXCEPT ![self] = futexes[mutex_index].state]
                       /\ pc' = [pc EXCEPT ![self] = "lock_loop"]
                       /\ UNCHANGED << mutex_index, futexes, stack, wait_index, 
                                       val, wake_index, wake_all_index, value, 
                                       old_state_, old_state >>

lock(self) == lock_start(self) \/ lock_compare_exchange(self)
                 \/ lock_loop(self) \/ lock_reload_1(self)
                 \/ lock_after_exchange(self) \/ lock_reload_2(self)

unlock_start(self) == /\ pc[self] = "unlock_start"
                      /\ old_state' = [old_state EXCEPT ![self] = futexes[mutex_index].state]
                      /\ futexes' = [futexes EXCEPT ![mutex_index].state = futexes[mutex_index].state - (futexes[mutex_index].state % 4)]
                      /\ pc' = [pc EXCEPT ![self] = "unlock_maybe_wake"]
                      /\ UNCHANGED << mutex_index, stack, wait_index, val, 
                                      wake_index, wake_all_index, value, 
                                      old_state_, old_state_l >>

unlock_maybe_wake(self) == /\ pc[self] = "unlock_maybe_wake"
                           /\ IF old_state[self] % 4 > 1
                                 THEN /\ /\ old_state' = [old_state EXCEPT ![self] = Head(stack[self]).old_state]
                                         /\ stack' = [stack EXCEPT ![self] = << [ procedure |->  "futex_wake_single",
                                                                                  pc        |->  Head(stack[self]).pc,
                                                                                  wake_index |->  wake_index[self] ] >>
                                                                              \o Tail(stack[self])]
                                         /\ wake_index' = [wake_index EXCEPT ![self] = mutex_index]
                                      /\ pc' = [pc EXCEPT ![self] = "check_for_sleepers"]
                                 ELSE /\ pc' = [pc EXCEPT ![self] = Head(stack[self]).pc]
                                      /\ old_state' = [old_state EXCEPT ![self] = Head(stack[self]).old_state]
                                      /\ stack' = [stack EXCEPT ![self] = Tail(stack[self])]
                                      /\ UNCHANGED wake_index
                           /\ UNCHANGED << mutex_index, futexes, wait_index, 
                                           val, wake_all_index, value, 
                                           old_state_, old_state_l >>

unlock(self) == unlock_start(self) \/ unlock_maybe_wake(self)

proc_start(self) == /\ pc[self] = "proc_start"
                    /\ stack' = [stack EXCEPT ![self] = << [ procedure |->  "lock",
                                                             pc        |->  "cs",
                                                             old_state_l |->  old_state_l[self] ] >>
                                                         \o stack[self]]
                    /\ old_state_l' = [old_state_l EXCEPT ![self] = 0]
                    /\ pc' = [pc EXCEPT ![self] = "lock_start"]
                    /\ UNCHANGED << mutex_index, futexes, wait_index, val, 
                                    wake_index, wake_all_index, value, 
                                    old_state_, old_state >>

cs(self) == /\ pc[self] = "cs"
            /\ stack' = [stack EXCEPT ![self] = << [ procedure |->  "unlock",
                                                     pc        |->  "maybe_loop",
                                                     old_state |->  old_state[self] ] >>
                                                 \o stack[self]]
            /\ old_state' = [old_state EXCEPT ![self] = 0]
            /\ pc' = [pc EXCEPT ![self] = "unlock_start"]
            /\ UNCHANGED << mutex_index, futexes, wait_index, val, wake_index, 
                            wake_all_index, value, old_state_, old_state_l >>

maybe_loop(self) == /\ pc[self] = "maybe_loop"
                    /\ \/ /\ pc' = [pc EXCEPT ![self] = "proc_start"]
                       \/ /\ pc' = [pc EXCEPT ![self] = "proc_done"]
                    /\ UNCHANGED << mutex_index, futexes, stack, wait_index, 
                                    val, wake_index, wake_all_index, value, 
                                    old_state_, old_state_l, old_state >>

proc_done(self) == /\ pc[self] = "proc_done"
                   /\ TRUE
                   /\ pc' = [pc EXCEPT ![self] = "Done"]
                   /\ UNCHANGED << mutex_index, futexes, stack, wait_index, 
                                   val, wake_index, wake_all_index, value, 
                                   old_state_, old_state_l, old_state >>

Proc(self) == proc_start(self) \/ cs(self) \/ maybe_loop(self)
                 \/ proc_done(self)

set_4(self) == /\ pc[self] = "set_4"
               /\ /\ stack' = [stack EXCEPT ![self] = << [ procedure |->  "set",
                                                           pc        |->  "check_4",
                                                           old_state_ |->  old_state_[self],
                                                           value     |->  value[self] ] >>
                                                       \o stack[self]]
                  /\ value' = [value EXCEPT ![self] = 4]
               /\ old_state_' = [old_state_ EXCEPT ![self] = 0]
               /\ pc' = [pc EXCEPT ![self] = "set_start"]
               /\ UNCHANGED << mutex_index, futexes, wait_index, val, 
                               wake_index, wake_all_index, old_state_l, 
                               old_state >>

check_4(self) == /\ pc[self] = "check_4"
                 /\ (futexes[mutex_index].state - (futexes[mutex_index].state % 4)) = 4
                 /\ pc' = [pc EXCEPT ![self] = "set_8"]
                 /\ UNCHANGED << mutex_index, futexes, stack, wait_index, val, 
                                 wake_index, wake_all_index, value, old_state_, 
                                 old_state_l, old_state >>

set_8(self) == /\ pc[self] = "set_8"
               /\ /\ stack' = [stack EXCEPT ![self] = << [ procedure |->  "set",
                                                           pc        |->  "check_8",
                                                           old_state_ |->  old_state_[self],
                                                           value     |->  value[self] ] >>
                                                       \o stack[self]]
                  /\ value' = [value EXCEPT ![self] = 8]
               /\ old_state_' = [old_state_ EXCEPT ![self] = 0]
               /\ pc' = [pc EXCEPT ![self] = "set_start"]
               /\ UNCHANGED << mutex_index, futexes, wait_index, val, 
                               wake_index, wake_all_index, old_state_l, 
                               old_state >>

check_8(self) == /\ pc[self] = "check_8"
                 /\ (futexes[mutex_index].state - (futexes[mutex_index].state % 4)) = 8
                 /\ pc' = [pc EXCEPT ![self] = "Done"]
                 /\ UNCHANGED << mutex_index, futexes, stack, wait_index, val, 
                                 wake_index, wake_all_index, value, old_state_, 
                                 old_state_l, old_state >>

Setter(self) == set_4(self) \/ check_4(self) \/ set_8(self)
                   \/ check_8(self)

(* Allow infinite stuttering to prevent deadlock on termination. *)
Terminating == /\ \A self \in ProcSet: pc[self] = "Done"
               /\ UNCHANGED vars

Next == (\E self \in ProcSet:  \/ futex_wait(self)
                               \/ futex_wake_single(self)
                               \/ futex_wake_all(self) \/ set(self)
                               \/ lock(self) \/ unlock(self))
           \/ (\E self \in Procs: Proc(self))
           \/ (\E self \in {1}: Setter(self))
           \/ Terminating

Spec == /\ Init /\ [][Next]_vars
        /\ \A self \in Procs : /\ WF_vars(Proc(self))
                               /\ WF_vars(lock(self))
                               /\ WF_vars(unlock(self))
                               /\ WF_vars(futex_wait(self))
                               /\ WF_vars(futex_wake_single(self))
        /\ \A self \in {1} : WF_vars(Setter(self)) /\ WF_vars(set(self))

Termination == <>(\A self \in ProcSet: pc[self] = "Done")

\* END TRANSLATION

TestClearBit == /\ ClearBit(0, 0) = 0
                /\ ClearBit(1, 0) = 0
                /\ ClearBit(2, 0) = 2
                /\ ClearBit(3, 0) = 2
                /\ ClearBit(4, 0) = 4
                /\ ClearBit(0, 1) = 0
                /\ ClearBit(1, 1) = 1
                /\ ClearBit(2, 1) = 0
                /\ ClearBit(3, 1) = 1
                /\ ClearBit(4, 1) = 4
                /\ ClearBit(5, 1) = 5
                /\ ClearBit(6, 1) = 4
                /\ ClearBit(7, 1) = 5
                /\ ClearBit(8, 1) = 8

MutualExclusion == \A i, j \in Procs : 
                     (i # j) => ~ /\ pc[i] = "cs"
                                  /\ pc[j] = "cs"

Trying(i) == stack[i] /= <<>> /\ Head(stack[i]).procedure = "lock"

DeadlockFree == \A i \in Procs : 
                     Trying(i) ~> (\E j \in Procs : pc[j] = "cs")
\*
\*StarvationFree == \A i \in WorkerProcs : 
\*                     Trying(i) ~> (pc[i] = "cs")
\*
\*WorkGetsTaken == work_to_do > 0 ~> work_to_do = 0
\*WorkGetsDone == work_to_do > 0 ~> work_done
\*
\*ShutdownCorrectly == done = GeneratorProcs ~> (\A self \in ProcSet : pc[self] = "Done")
\*
\*NotInPotentialSteal == \A i \in WorkerProcs : pc[i] /= "cv_wait_potential_steal_cmp_exchg"
\*MutualExclusion2 == \A i, j \in WorkerProcs : 
\*                     (i # j) => ~ /\ pc[i] = "cv_wait_potential_steal_cmp_exchg"
\*                                  /\ pc[j] = "cv_wait_potential_steal_cmp_exchg"
\*                                  
\*WorkDoneAtEnd == (\A i \in WorkerProcs : pc[i] = "Done") => work_done \/ work_to_do = 0
\*
\*InPotentialStealAndAdds == \E i \in WorkerProcs: pc[i] = "cv_wait_potential_steal_cmp_exchg" /\ futexes[g_signals_index[g_[i]]].state = signals[i]
\*
\*PotentialStealThenWorkGetsDone == (\E i \in WorkerProcs: pc[i] = "cv_wait_potential_steal_cmp_exchg" /\ futexes[g_signals_index[g_[i]]].state = signals[i]) ~> (\A i \in WorkerProcs : pc[i] = "Done")

SomeoneGetsTheLock == (\E i \in Procs: pc[i] = "acquire_masterlock_start") ~> (\E i \in Procs: pc[i] = "proc_loop")
YieldingWorks == (\E i \in Procs: pc[i] = "yield_loop") ~> (\E i \in Procs: pc[i] = "proc_loop")

=============================================================================
\* Modification History
\* Last modified Sat Dec 03 22:14:00 EST 2022 by malte
\* Created Mon Oct 12 21:12:21 EDT 2020 by malte
