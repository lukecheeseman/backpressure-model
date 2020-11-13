---- MODULE backpressure ----

EXTENDS FiniteSets, Integers, Sequences, TLC

Null == 0
Cowns == 1..4
BehaviourLimit == 4
OverloadThreshold == 2
PriorityLevels == {-1, 0, 1}

Min(s) == CHOOSE x \in s: \A y \in s \ {x}: y > x
Max(s) == CHOOSE x \in s: \A y \in s \ {x}: y < x

Range(f) == {f[x]: x \in DOMAIN f}

VARIABLES fuel, queue, scheduled, running, priority, blocker, mutor, mute
vars == <<fuel, queue, scheduled, running, priority, blocker, mutor, mute>>

EmptyQueue(c) == Len(queue[c]) = 0

Sleeping(c) == scheduled[c] /\ EmptyQueue(c)

Available(c) == scheduled[c] /\ ~EmptyQueue(c)

Overloaded(c) == Len(queue[c]) > OverloadThreshold

CurrentMessage(c) == IF EmptyQueue(c) THEN {} ELSE Head(queue[c])

LowPriority(cs) == {c \in cs: priority[c] = -1}

HighPriority(cs) == {c \in cs: priority[c] = 1}

RequiresPriority(c) == Overloaded(c) \/ \E m \in Range(queue[c]): \E k \in m \ {c}: priority[k] = 1

RECURSIVE Blockers(_)
Blockers(c) == IF blocker[c] = Null THEN {} ELSE {blocker[c]} \union Blockers(blocker[c])
Prioritise(c1) == IF priority[c1] < 1 THEN {c1} \union Blockers(c1) ELSE {}

Mutor(c) == ((priority[c] = 1) /\ Overloaded(c)) \/ (priority[c] = -1)

Init ==
  /\ fuel = BehaviourLimit
  /\ queue = [c \in Cowns |-> <<{c}>>]
  /\ scheduled = [c \in Cowns |-> TRUE]
  /\ running = [c \in Cowns |-> FALSE]
  /\ priority = [c \in Cowns |-> 0]
  /\ blocker = [c \in Cowns |-> Null]
  /\ mutor = [c \in Cowns |-> Null]
  /\ mute = [c \in Cowns |-> {}]

AcquireHigh(cown) ==
  scheduled[cown]
  /\ Len(queue[cown]) /= 0
  /\ LET msg == Head(queue[cown]) IN
  /\ cown < Max(msg)
  /\ LET next == Min({c \in msg: c > cown}) IN
    /\ priority[cown] = 1
    /\ LET prioritizing == Prioritise(Min({c \in msg: c > cown})) IN
       LET unmuting == { c \in prioritizing : priority[c] = -1 } IN
        /\ priority' = [c \in prioritizing |-> 1] @@ priority
        /\ scheduled' = (cown :> FALSE) @@ [c \in unmuting |-> TRUE] @@ scheduled
        /\ blocker' = (cown :> next) @@ blocker
        /\ queue' = (next :> Append(queue[next], msg)) @@ (cown :> Tail(queue[cown])) @@ queue
        /\ UNCHANGED <<fuel, running, mutor, mute>>

AcquireNormal(cown) ==
  scheduled[cown]
  /\ Len(queue[cown]) /= 0
  /\ LET msg == Head(queue[cown]) IN
  /\ cown < Max(msg)
  /\ LET next == Min({c \in msg: c > cown}) IN
    /\ priority[cown] /= 1
    /\ scheduled' = (cown :> FALSE) @@ scheduled
    /\ blocker' = (cown :> next) @@ blocker
    /\ queue' = (next :> Append(queue[next], msg)) @@ (cown :> Tail(queue[cown])) @@ queue
    /\ UNCHANGED <<fuel, running, priority, mutor, mute>>

Acquire(cown) == AcquireHigh(cown) \/ AcquireNormal(cown)

StartHigh(cown) ==
  /\ scheduled[cown]
  /\ ~running[cown]
  /\ Len(queue[cown]) /= 0
  /\ RequiresPriority(cown)
  /\ LET msg == Head(queue[cown]) IN
    /\ cown = Max(msg)
    /\ priority' = (cown :> 1) @@ priority
    /\ running' = (cown :> TRUE) @@ running
    /\ blocker' = [c \in msg |-> Null] @@ blocker
    /\ UNCHANGED <<fuel, queue, scheduled, mutor, mute>>

StartNormal(cown) ==
  /\ scheduled[cown]
  /\ ~running[cown]
  /\ Len(queue[cown]) /= 0
  /\ ~RequiresPriority(cown)
  /\ LET msg == Head(queue[cown]) IN
    /\ cown = Max(msg)
    /\ priority' = (cown :> 0) @@ priority
    /\ running' = (cown :> TRUE) @@ running
    /\ blocker' = [c \in msg |-> Null] @@ blocker
    /\ UNCHANGED <<fuel, queue, scheduled, mutor, mute>>

Start(cown) == StartHigh(cown) \/ StartNormal(cown)

SendAndMute(cown) == \* here senders can be empty
  LET senders == CurrentMessage(cown) IN
  /\ running[cown]
  /\ fuel > 0
  /\ \E receivers \in SUBSET Cowns: receivers /= {}
    /\ LET first == Min(receivers) IN
      priority[first] = 1
      /\ mutor[cown] = Null 
      /\ (\A c \in senders: priority[c] = 0)
      /\ receivers \ senders = receivers
      /\ \E c1 \in receivers: Mutor(c1) /\ (\A c2 \in receivers: c2 < c1 => ~Mutor(c2))
      /\ mutor' = (cown :> c1) @@ mutor
      /\ LET prioritizing == Prioritise(first) IN
        scheduled' = [c \in LowPriority(prioritizing) |-> TRUE] @@ scheduled
        /\ priority' = [c \in prioritizing |-> 1] @@ priority
      /\ queue' = (first :> Append(queue[first], receivers)) @@ queue
  /\ fuel' = fuel - 1
  /\ UNCHANGED <<running, blocker, mute>>

SendNoMute(cown) == \* here senders can be empty
  LET senders == CurrentMessage(cown) IN
  /\ running[cown]
  /\ fuel > 0
  /\ \E receivers \in SUBSET Cowns: receivers /= {}
    /\ LET first == Min(receivers) IN
    /\ priority[first] = 1
    /\ (mutor[cown] /= Null 
        \/ (\E c \in senders: priority[c] /= 0 \/ c \in receivers) \* TODO: justify
        \/ (\A c \in receivers: ~Mutor(c)))
      /\ LET prioritizing == Prioritise(first) IN
        scheduled' = [c \in LowPriority(prioritizing) |-> TRUE] @@ scheduled
        /\ priority' = [c \in prioritizing |-> 1] @@ priority
    /\ queue' = (first :> Append(queue[first], receivers)) @@ queue
  /\ fuel' = fuel - 1
  /\ UNCHANGED <<running, blocker, mute, mutor>>

SendNormal(cown) == \* here senders can be empty
  LET senders == CurrentMessage(cown) IN
  /\ running[cown]
  /\ fuel > 0
  /\ \E receivers \in SUBSET Cowns: receivers /= {}
    /\ LET first == Min(receivers) IN
      priority[first] /= 1
      /\ queue' = (first :> Append(queue[first], receivers)) @@ queue
  /\ fuel' = fuel - 1
  /\ UNCHANGED <<scheduled, priority, mutor, running, blocker, mute>>

Send(cown) == SendAndMute(cown) \/ SendNoMute(cown) \/ SendNormal(cown)

CompleteMute(cown) ==
  running[cown]
  /\ mutor[cown] /= Null
  /\ LET msg == CurrentMessage(cown) IN
     LET muting == {c \in msg: priority[c] = 0} IN
      /\ priority' = [c \in muting |-> -1] @@ priority
      /\ mute' = (mutor[cown] :> mute[mutor[cown]] \union muting) @@ mute
      /\ scheduled' = [c \in msg |-> c \notin muting] @@ scheduled
  /\ queue' = (cown :> Tail(queue[cown])) @@ queue
  /\ running' = (cown :> FALSE) @@ running
  /\ mutor' = (cown :> Null) @@ mutor
  /\ UNCHANGED <<fuel, blocker>>

CompleteNormal(cown) ==
  running[cown]
  /\ mutor[cown] = Null
  /\ LET msg == CurrentMessage(cown) IN
    /\ scheduled' = [c \in msg |-> TRUE] @@ scheduled
    /\ priority' = (cown :> IF Len(queue[cown]) = 1 THEN 0 ELSE priority[cown]) @@
                    [c \in msg \ {cown} |-> IF EmptyQueue(c) THEN 0 ELSE priority[c]] @@
                    priority
  /\ queue' = (cown :> Tail(queue[cown])) @@ queue
  /\ running' = (cown :> FALSE) @@ running
  /\ mutor' = (cown :> Null) @@ mutor
  /\ UNCHANGED <<fuel, blocker, mute>>

Complete(cown) == CompleteMute(cown) \/ CompleteNormal(cown)

Unmute ==
  LET invalid_keys == {c \in DOMAIN mute: priority[c] = 0} IN
  LET unmuting == UNION Range([k \in invalid_keys |-> LowPriority(mute[k])]) IN
  /\ unmuting /= {}
  /\ priority' = [c \in unmuting |-> 0] @@ priority
  /\ mute' = [c \in invalid_keys |-> {}] @@ mute
  /\ scheduled' = [c \in unmuting |-> TRUE] @@ scheduled
  /\ UNCHANGED <<fuel, queue, running, blocker, mutor>>

Run(cown) ==
  \/ Acquire(cown)
  \/ Start(cown)
  \/ Send(cown)
  \/ Complete(cown)

Terminating ==
  \* TODO: only require empty queue
  \* /\ \A c \in Cowns: EmptyQueue(c)
  \* /\ Assert(\A c \in Cowns: Sleeping(c), "Termination with unscheduled cowns")
  /\ \A c \in Cowns: Sleeping(c)
  /\ UNCHANGED vars

Next == \E c \in Cowns: Run(c) \/ Unmute

Spec ==
  /\ Init
  /\ [][Next \/ Terminating]_vars
  /\ \A c \in Cowns: WF_vars(Run(c))
  /\ WF_vars(Unmute)

\* Utility Functions

Pick(s) == CHOOSE x \in s: TRUE

ReduceSet(op(_, _), set, acc) ==
  LET f[s \in SUBSET set] ==
    IF s = {} THEN acc ELSE LET x == Pick(s) IN op(x, f[s \ {x}])
  IN f[set]

MutedBy(a, b) == (a \in mute[b]) /\ (priority[a] = -1)
Muted(c) == \E k \in Cowns: MutedBy(c, k)

AcquiredBy(a, b) == (a < b) /\ (a \in UNION Range(queue[b]))
Acquired(c) == \E k \in Cowns: AcquiredBy(c, k)

Required(c) == \E k \in Cowns: (k < c) /\ (c \in UNION Range(queue[k]))

\* https://github.com/tlaplus/Examples/blob/master/specifications/TransitiveClosure/TransitiveClosure.tla#L114
TC(R) ==
  LET
    S == {r[1]: r \in R} \cup {r[2]: r \in R}
    RECURSIVE TCR(_)
    TCR(T) ==
      IF T = {} THEN R
      ELSE
        LET
          r == CHOOSE s \in T: TRUE
          RR == TCR(T \ {r})
        IN
          RR \cup {<<s, t>> \in S \X S: <<s, r>> \in RR /\ <<r, t>> \in RR}
  IN
    TCR(S)

CylcicTransitiveClosure(R(_, _)) ==
  LET s == {<<a, b>> \in Cowns \X Cowns: R(a, b)}
  IN \E c \in Cowns: <<c, c>> \in TC(s)

\* Temporal Properties

\* The model does not livelock.
Termination == <>[](\A c \in Cowns: Sleeping(c))

\* Invariants

\* The message limit for TLC is enforced (the model has finite state space).
MessageLimit ==
  LET msgs == ReduceSet(LAMBDA c, sum: sum + Len(queue[c]), Cowns, 0) IN
  msgs <= (BehaviourLimit + Max(Cowns))

\* The running cown is scheduled and the greatest cown in the head of its queue.
RunningIsScheduled ==
  \A c \in Cowns: running[c] => scheduled[c] /\ (c = Max(CurrentMessage(c)))

\* A cown is not its own mutor.
CownNotMutedBySelf == \A c \in Cowns: c \notin mute[c]

\* A low-priority cown is muted.
LowPriorityMuted == \A c \in Cowns: (priority[c] = -1) => Muted(c)

\* There cannot be message that has acquired a high-priority cown and has
\* acquired, or is in the queue of, a low-priority cown.
Nonblocking ==
  \A c \in Cowns: \A m \in Range(queue[c]):
    \A <<l, h>> \in LowPriority(m) \X HighPriority(m): (c <= h) \/ (c < l)

\* All cowns in a running message have no blocker.
RunningNotBlocked ==
  \A c \in Cowns: running[c] => (\A k \in CurrentMessage(c): blocker[k] = Null)

\* An unscheduled cown is either muted or acquired.
UnscheduledByMuteOrAcquire ==
  \A c \in Cowns: ~((priority[c] = -1) \/ Acquired(c)) <=> scheduled[c]

\* A cown in the queue of a greater cown is unscheduled.
BehaviourAcquisition ==
  \A c \in Cowns: \A k \in UNION Range(queue[c]): (k < c) => ~scheduled[k]

\* A cown can only be acquired by at most one cown.
AcquiredOnce ==
  \A <<a, b, c>> \in Cowns \X Cowns \X Cowns:
    (AcquiredBy(a, b) /\ AcquiredBy(a, c)) => (b = c)

\* All messages in a cown's queue must contain the cown.
SelfInQueueMessages == \A c \in Cowns: \A m \in Range(queue[c]): c \in m

\* A high-priority cown is in a queue of a high-priority cown.
HighPriorityInUnblockedQueue ==
  \A c \in HighPriority(Cowns):
    \E k \in HighPriority(Cowns): c \in UNION Range(queue[k])

\* Warning: not enforced by implementation.
SleepingIsNormal == \A c \in Cowns: Sleeping(c) => (priority[c] = 0)

\* High-priority cowns has messages in its queue or is acquired.
HighPriorityHasWork == \A c \in HighPriority(Cowns):
  \/ ~EmptyQueue(c)
  \/ Acquired(c)

\* A muted cown has only one mutor in the mute map.
MuteSetsDisjoint == \A <<a, b>> \in Cowns \X Cowns:
  ((mute[a] \intersect mute[b]) /= {}) => (a = b)

MutedByCycle(c1) == LET s == {<<a, b>> \in Cowns \X Cowns: MutedBy(a, b)} IN
                      \E c2 \in Cowns: <<c1, c2>> \in TC(s) /\ <<c2, c2>> \in TC(s)

\* The transitive closure of the relation MutedBy has no cycles.
MutedByIsAcyclic == \A c \in Cowns: ~MutedByCycle(c)

BlockerIsNextRequiredToRun ==
  \A c1, c2 \in Cowns: blocker[c1] = c2 <=>
    \E c3 \in Cowns: c3 > c1 /\
    \E m \in Range(queue[c3]): ~(running[c3] /\ m = Head(queue[c3])) /\ c1 \in m /\ c2 = Min({c4 \in m: c4 > c1})

====
