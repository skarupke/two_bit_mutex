(* Copyright (C) 2022 Malte Skarupke

   This is free software; you can redistribute it and/or
   modify it under the terms of the GNU Lesser General Public
   License as published by the Free Software Foundation; either
   version 2.1 of the License, or (at your option) any later version.

   See https://www.gnu.org/licenses/.  *)

-------------------------- MODULE one_byte_mutex --------------------------

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

procedure lock()
variable old_state = 0;
{
lock_first_exchange:
  old_state := futexes[mutex_index].state;
  futexes[mutex_index].state := 1;
lock_first_comparison:
  if (old_state = 0)
    return;
lock_second_exchange:
  old_state := futexes[mutex_index].state;
  futexes[mutex_index].state := 2;
lock_second_comparison:
  if (old_state = 0)
    return;
  else
  {
    call futex_wait(mutex_index, 2);
    goto lock_second_exchange;
  }
};

procedure unlock ()
variable old_state = 0;
{
unlock_exchange:
  old_state := futexes[mutex_index].state;
  futexes[mutex_index].state := 0;
unlock_comparison:
  if (old_state = 2)
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
}
*)

\* BEGIN TRANSLATION (chksum(pcal) = "79e22e" /\ chksum(tla) = "fbf03e58")
\* Label futex_wake_all of procedure futex_wake_all at line 67 col 5 changed to futex_wake_all_
\* Procedure variable old_state of procedure lock at line 72 col 10 changed to old_state_
VARIABLES mutex_index, futexes, pc, stack, wait_index, val, wake_index, 
          wake_all_index, old_state_, old_state

vars == << mutex_index, futexes, pc, stack, wait_index, val, wake_index, 
           wake_all_index, old_state_, old_state >>

ProcSet == (Procs)

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
        (* Procedure lock *)
        /\ old_state_ = [ self \in ProcSet |-> 0]
        (* Procedure unlock *)
        /\ old_state = [ self \in ProcSet |-> 0]
        /\ stack = [self \in ProcSet |-> << >>]
        /\ pc = [self \in ProcSet |-> "proc_start"]

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
                                     old_state_, old_state >>

wait_for_wake(self) == /\ pc[self] = "wait_for_wake"
                       /\ ~ (self \in futexes[wait_index[self]].sleepers)
                       /\ pc' = [pc EXCEPT ![self] = Head(stack[self]).pc]
                       /\ wait_index' = [wait_index EXCEPT ![self] = Head(stack[self]).wait_index]
                       /\ val' = [val EXCEPT ![self] = Head(stack[self]).val]
                       /\ stack' = [stack EXCEPT ![self] = Tail(stack[self])]
                       /\ UNCHANGED << mutex_index, futexes, wake_index, 
                                       wake_all_index, old_state_, old_state >>

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
                                            wake_all_index, old_state_, 
                                            old_state >>

futex_wake_single(self) == check_for_sleepers(self)

futex_wake_all_(self) == /\ pc[self] = "futex_wake_all_"
                         /\ futexes' = [futexes EXCEPT ![wake_all_index[self]].sleepers = {}]
                         /\ pc' = [pc EXCEPT ![self] = Head(stack[self]).pc]
                         /\ wake_all_index' = [wake_all_index EXCEPT ![self] = Head(stack[self]).wake_all_index]
                         /\ stack' = [stack EXCEPT ![self] = Tail(stack[self])]
                         /\ UNCHANGED << mutex_index, wait_index, val, 
                                         wake_index, old_state_, old_state >>

futex_wake_all(self) == futex_wake_all_(self)

lock_first_exchange(self) == /\ pc[self] = "lock_first_exchange"
                             /\ old_state_' = [old_state_ EXCEPT ![self] = futexes[mutex_index].state]
                             /\ futexes' = [futexes EXCEPT ![mutex_index].state = 1]
                             /\ pc' = [pc EXCEPT ![self] = "lock_first_comparison"]
                             /\ UNCHANGED << mutex_index, stack, wait_index, 
                                             val, wake_index, wake_all_index, 
                                             old_state >>

lock_first_comparison(self) == /\ pc[self] = "lock_first_comparison"
                               /\ IF old_state_[self] = 0
                                     THEN /\ pc' = [pc EXCEPT ![self] = Head(stack[self]).pc]
                                          /\ old_state_' = [old_state_ EXCEPT ![self] = Head(stack[self]).old_state_]
                                          /\ stack' = [stack EXCEPT ![self] = Tail(stack[self])]
                                     ELSE /\ pc' = [pc EXCEPT ![self] = "lock_second_exchange"]
                                          /\ UNCHANGED << stack, old_state_ >>
                               /\ UNCHANGED << mutex_index, futexes, 
                                               wait_index, val, wake_index, 
                                               wake_all_index, old_state >>

lock_second_exchange(self) == /\ pc[self] = "lock_second_exchange"
                              /\ old_state_' = [old_state_ EXCEPT ![self] = futexes[mutex_index].state]
                              /\ futexes' = [futexes EXCEPT ![mutex_index].state = 2]
                              /\ pc' = [pc EXCEPT ![self] = "lock_second_comparison"]
                              /\ UNCHANGED << mutex_index, stack, wait_index, 
                                              val, wake_index, wake_all_index, 
                                              old_state >>

lock_second_comparison(self) == /\ pc[self] = "lock_second_comparison"
                                /\ IF old_state_[self] = 0
                                      THEN /\ pc' = [pc EXCEPT ![self] = Head(stack[self]).pc]
                                           /\ old_state_' = [old_state_ EXCEPT ![self] = Head(stack[self]).old_state_]
                                           /\ stack' = [stack EXCEPT ![self] = Tail(stack[self])]
                                           /\ UNCHANGED << wait_index, val >>
                                      ELSE /\ /\ stack' = [stack EXCEPT ![self] = << [ procedure |->  "futex_wait",
                                                                                       pc        |->  "lock_second_exchange",
                                                                                       wait_index |->  wait_index[self],
                                                                                       val       |->  val[self] ] >>
                                                                                   \o stack[self]]
                                              /\ val' = [val EXCEPT ![self] = 2]
                                              /\ wait_index' = [wait_index EXCEPT ![self] = mutex_index]
                                           /\ pc' = [pc EXCEPT ![self] = "check_state"]
                                           /\ UNCHANGED old_state_
                                /\ UNCHANGED << mutex_index, futexes, 
                                                wake_index, wake_all_index, 
                                                old_state >>

lock(self) == lock_first_exchange(self) \/ lock_first_comparison(self)
                 \/ lock_second_exchange(self)
                 \/ lock_second_comparison(self)

unlock_exchange(self) == /\ pc[self] = "unlock_exchange"
                         /\ old_state' = [old_state EXCEPT ![self] = futexes[mutex_index].state]
                         /\ futexes' = [futexes EXCEPT ![mutex_index].state = 0]
                         /\ pc' = [pc EXCEPT ![self] = "unlock_comparison"]
                         /\ UNCHANGED << mutex_index, stack, wait_index, val, 
                                         wake_index, wake_all_index, 
                                         old_state_ >>

unlock_comparison(self) == /\ pc[self] = "unlock_comparison"
                           /\ IF old_state[self] = 2
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
                                           val, wake_all_index, old_state_ >>

unlock(self) == unlock_exchange(self) \/ unlock_comparison(self)

proc_start(self) == /\ pc[self] = "proc_start"
                    /\ stack' = [stack EXCEPT ![self] = << [ procedure |->  "lock",
                                                             pc        |->  "cs",
                                                             old_state_ |->  old_state_[self] ] >>
                                                         \o stack[self]]
                    /\ old_state_' = [old_state_ EXCEPT ![self] = 0]
                    /\ pc' = [pc EXCEPT ![self] = "lock_first_exchange"]
                    /\ UNCHANGED << mutex_index, futexes, wait_index, val, 
                                    wake_index, wake_all_index, old_state >>

cs(self) == /\ pc[self] = "cs"
            /\ stack' = [stack EXCEPT ![self] = << [ procedure |->  "unlock",
                                                     pc        |->  "maybe_loop",
                                                     old_state |->  old_state[self] ] >>
                                                 \o stack[self]]
            /\ old_state' = [old_state EXCEPT ![self] = 0]
            /\ pc' = [pc EXCEPT ![self] = "unlock_exchange"]
            /\ UNCHANGED << mutex_index, futexes, wait_index, val, wake_index, 
                            wake_all_index, old_state_ >>

maybe_loop(self) == /\ pc[self] = "maybe_loop"
                    /\ \/ /\ pc' = [pc EXCEPT ![self] = "proc_start"]
                       \/ /\ pc' = [pc EXCEPT ![self] = "proc_done"]
                    /\ UNCHANGED << mutex_index, futexes, stack, wait_index, 
                                    val, wake_index, wake_all_index, 
                                    old_state_, old_state >>

proc_done(self) == /\ pc[self] = "proc_done"
                   /\ TRUE
                   /\ pc' = [pc EXCEPT ![self] = "Done"]
                   /\ UNCHANGED << mutex_index, futexes, stack, wait_index, 
                                   val, wake_index, wake_all_index, old_state_, 
                                   old_state >>

Proc(self) == proc_start(self) \/ cs(self) \/ maybe_loop(self)
                 \/ proc_done(self)

(* Allow infinite stuttering to prevent deadlock on termination. *)
Terminating == /\ \A self \in ProcSet: pc[self] = "Done"
               /\ UNCHANGED vars

Next == (\E self \in ProcSet:  \/ futex_wait(self)
                               \/ futex_wake_single(self)
                               \/ futex_wake_all(self) \/ lock(self)
                               \/ unlock(self))
           \/ (\E self \in Procs: Proc(self))
           \/ Terminating

Spec == /\ Init /\ [][Next]_vars
        /\ \A self \in Procs : /\ WF_vars(Proc(self))
                               /\ WF_vars(lock(self))
                               /\ WF_vars(unlock(self))
                               /\ WF_vars(futex_wait(self))
                               /\ WF_vars(futex_wake_single(self))

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

=============================================================================
\* Modification History
\* Last modified Tue Dec 06 20:33:47 EST 2022 by malte
\* Created Mon Oct 12 21:12:21 EDT 2020 by malte
