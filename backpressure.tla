---- MODULE backpressure ----

EXTENDS FiniteSets, Naturals, Sequences, TLC

CONSTANTS Null
BehaviourLimit == 4
Cowns == 1..3
OverloadThreshold == 2

Min(s) == CHOOSE x \in s: \A y \in s \ {x}: y > x
Max(s) == CHOOSE x \in s: \A y \in s \ {x}: y < x

Range(f) == {f[x]: x \in DOMAIN f}

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
Muted(c) == c \in UNION Range(mute)
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
  /\ LET msg == Head(queue[cown]) IN
    /\ cown < Max(msg)
    /\ scheduled' = (cown :> FALSE) @@ scheduled
    /\ LET next == Min({c \in msg: c > cown}) IN
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
  /\ \E msg \in SUBSET Cowns:
    /\ Cardinality(msg) > 0
    /\ Cardinality(msg) <= 3 \* cut state space
    /\ ScanMsg(cown, Head(queue[cown]), msg)
    /\ queue' = (Min(msg) :> Append(queue[Min(msg)], msg)) @@ queue
  /\ fuel' = fuel - 1
  /\ UNCHANGED <<scheduled, mute>>

Complete(cown) ==
  /\ Running(cown)
  /\ LET msg == Head(queue[cown]) IN
    IF mutor[cown] /= Null THEN
      LET muting == {c \in msg: ~Overloaded(c)} IN
      /\ scheduled' = [c \in msg |-> c \notin muting] @@ scheduled
      /\ mute' = (mutor[cown] :> mute[mutor[cown]] \union muting) @@ mute
    ELSE
      /\ scheduled' = [c \in msg |-> TRUE] @@ scheduled
      /\ UNCHANGED <<mute>>
  /\ queue' = (cown :> Tail(queue[cown])) @@ queue
  /\ mutor' = (cown :> Null) @@ mutor
  /\ UNCHANGED <<fuel>>

Unmute(cown) ==
  LET invalid_keys == {k \in DOMAIN mute: ~TriggersMuting(k)} IN
  LET unmuting == UNION Range([k \in invalid_keys |-> mute[k]]) IN
  /\ invalid_keys /= {}
  /\ mute' = [k \in invalid_keys |-> {}] @@ mute
  /\ scheduled' = [c \in unmuting |-> TRUE] @@ scheduled
  /\ UNCHANGED <<fuel, queue, mutor>>

Run(cown) ==
  \/ Acquire(cown)
  \/ Send(cown)
  \/ Complete(cown)
  \/ Unmute(cown)

Next == Terminating \/ \E c \in Cowns: Run(c)

Spec ==
  /\ Init
  /\ [][Next]_vars
  /\ \A c \in Cowns: WF_vars(Run(c))

MessageLimit ==
  LET msgs == ReduceSet(LAMBDA c, sum: sum + Len(queue[c]), Cowns, 0) IN
  msgs <= (BehaviourLimit + Max(Cowns))

MutedNotScheduled ==
  \A c \in Cowns: Muted(c) => ~scheduled[c]

\* TODO: no message from overloaded cown is in muted queue
\* PriorityMessageUnblocked ==
\*   \A c \in Cowns: Muted(c) => ...

OverloadedCownsEventuallyRun ==
  \A c \in Cowns: Overloaded(c) ~> scheduled[c]

====
