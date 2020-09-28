---- MODULE backpressure ----

EXTENDS FiniteSets, Naturals, Sequences, TLC

CONSTANTS Null
BehaviourLimit == 5
Cowns == 1..3
OverloadThreshold == 2

Min(s) == CHOOSE x \in s: \A y \in s \ {x}: y > x
Max(s) == CHOOSE x \in s: \A y \in s \ {x}: y < x

Pick(s) == CHOOSE x \in s: TRUE
ReduceSet(op(_, _), set, acc) ==
  LET f[s \in SUBSET set] ==
    IF s = {} THEN acc ELSE LET x == Pick(s) IN op(x, f[s \ {x}])
  IN f[set]

VARIABLES fuel, queue, scheduled, mute, mutor
vars == <<fuel, queue, scheduled, mute, mutor>>

Sleeping(c) == scheduled[c] /\ (Len(queue[c]) = 0)
Available(c) == scheduled[c] /\ (Len(queue[c]) > 0)
Running(c) ==
  /\ scheduled[c]
  /\ IF Len(queue[c]) = 0 THEN FALSE ELSE c = Max(Head(queue[c]))

Overloaded(c) == Len(queue[c]) >= OverloadThreshold
Muted(c) == ~scheduled[c] /\ (Len(queue[c]) > 0)
TriggersMuting(c) == Overloaded(c) \/ Muted(c)

Init ==
  /\ fuel = BehaviourLimit
  /\ queue = [c \in Cowns |-> <<{c}>>]
  /\ scheduled = [c \in Cowns |-> TRUE]
  /\ mute = [c \in Cowns |-> {}]
  /\ mutor = [c \in Cowns |-> Null]

Terminating ==
  /\ \A c \in Cowns: Sleeping(c)
  /\ UNCHANGED vars

Acquire(cown) ==
  /\ Available(cown)
  /\
    LET msg == Head(queue[cown]) IN
    /\ cown < Max({c \in msg: scheduled[c]})
    /\ scheduled' = (cown :> FALSE) @@ scheduled
    /\
      LET next == Min({c \in msg: c > cown}) IN
      LET q == (cown :> Tail(queue[cown])) @@ queue IN
      queue' = (next :> Append(queue[next], msg)) @@ q
  /\ UNCHANGED <<fuel, mute, mutor>>

ScanMsg(cown, senders, receivers) ==
  IF \E r \in receivers: TriggersMuting(r) THEN
    LET m == CHOOSE r \in receivers: TriggersMuting(r) IN
    mutor' = (cown :> m) @@ mutor
  ELSE
    UNCHANGED <<mutor>>

Send(cown) ==
  /\ Running(cown)
  /\ fuel > 0
  /\
    \E msg \in SUBSET Cowns:
    /\ Cardinality(msg) > 0
    /\ Cardinality(msg) <= 3 \* cut state space
    /\ ScanMsg(cown, Head(queue[cown]), msg)
    /\ queue' = (Min(msg) :> Append(queue[Min(msg)], msg)) @@ queue
  /\ fuel' = fuel - 1
  /\ UNCHANGED <<scheduled, mute>>

Complete(cown) ==
  /\ Running(cown)
  /\ scheduled' = [c \in Head(queue[cown]) |-> TRUE] @@ scheduled
  /\ queue' = (cown :> Tail(queue[cown])) @@ queue
  \* TODO: mute
  /\ mutor' = (cown :> Null) @@ mutor
  /\ UNCHANGED <<fuel, mute>>

Behaviour(cown) ==
  \/ Acquire(cown)
  \/ Send(cown)
  \/ Complete(cown)

Next == Terminating \/ \E c \in Cowns: Behaviour(c)

Spec ==
  /\ Init
  /\ [][Next]_vars
  /\ \A c \in Cowns: WF_vars(Behaviour(c))

MessageLimit ==
  LET msgs == ReduceSet(LAMBDA c, sum: sum + Len(queue[c]), Cowns, 0) IN
  msgs <= (BehaviourLimit + Max(Cowns))

OverloadedCownsEventuallyRun ==
  \A c \in Cowns: Overloaded(c) ~> scheduled[c]

====
