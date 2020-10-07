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

Pick(s) == CHOOSE x \in s: TRUE

ReduceSet(op(_, _), set, acc) ==
  LET f[s \in SUBSET set] ==
    IF s = {} THEN acc ELSE LET x == Pick(s) IN op(x, f[s \ {x}])
  IN f[set]

VARIABLES fuel, queue, scheduled, running, priority, blocker, mutor, mute
vars == <<fuel, queue, scheduled, running, priority, blocker, mutor, mute>>

Sleeping(c) == scheduled[c] /\ (Len(queue[c]) = 0)

Available(c) == scheduled[c] /\ (Len(queue[c]) > 0)

Overloaded(c) == Len(queue[c]) > OverloadThreshold

Muted(c) == c \in UNION Range(mute)

CurrentMessage(c) == IF Len(queue[c]) > 0 THEN Head(queue[c]) ELSE {}

LowPriority(cs) == {c \in cs: priority[c] = -1}

HighPriority(cs) == {c \in cs: priority[c] = 1}

RequiresPriority(c) ==
  \/ Overloaded(c)
  \/ \E m \in Range(queue[c]): \E k \in m \ {c}: priority[k] = 1

RECURSIVE Blockers(_)
Blockers(c) ==
  IF blocker[c] = Null THEN {} ELSE {blocker[c]} \union Blockers(blocker[c])
Prioritizing(cs) ==
  LET unprioritized == {c \in cs: priority[c] < 1} IN
  unprioritized \union UNION {Blockers(c): c \in unprioritized}

ValidMutor(c) ==
  \/ (priority[c] = 1) /\ Overloaded(c)
  \/ (priority[c] = -1)

Init ==
  /\ fuel = BehaviourLimit
  /\ queue = [c \in Cowns |-> <<{c}>>]
  /\ scheduled = [c \in Cowns |-> TRUE]
  /\ running = [c \in Cowns |-> FALSE]
  /\ priority = [c \in Cowns |-> Null]
  /\ blocker = [c \in Cowns |-> Null]
  /\ mutor = [c \in Cowns |-> Null]
  /\ mute = [c \in Cowns |-> {}]

Terminating ==
  /\ \A c \in Cowns: Sleeping(c)
  /\ UNCHANGED vars

Acquire(cown) ==
  LET msg == CurrentMessage(cown) IN
  /\ Available(cown)
  /\ cown < Max(msg)
  /\ IF \E c \in msg: priority[c] = 1 THEN
      LET prioritizing == Prioritizing({c \in msg: c > cown}) IN
      LET unmuting == LowPriority(prioritizing) IN
      /\ priority' = [c \in prioritizing |-> 1] @@ priority
      /\ scheduled' = (cown :> FALSE) @@ [c \in unmuting |-> TRUE] @@ scheduled
    ELSE
      /\ scheduled' = (cown :> FALSE) @@ scheduled
      /\ UNCHANGED <<priority, mute>>
  /\ LET next == Min({c \in msg: c > cown}) IN
    /\ blocker' = (cown :> next) @@ blocker
    /\ LET q == (cown :> Tail(queue[cown])) @@ queue IN
      queue' = (next :> Append(queue[next], msg)) @@ q
  /\ UNCHANGED <<fuel, running, mutor, mute>>

Prerun(cown) ==
  LET msg == CurrentMessage(cown) IN
  /\ scheduled[cown]
  /\ ~running[cown]
  /\ IF msg = {} THEN FALSE ELSE cown = Max(msg)
  /\ priority' = (cown :> IF RequiresPriority(cown) THEN 1 ELSE 0) @@ priority
  /\ running' = (cown :> TRUE) @@ running
  /\ blocker' = [c \in msg |-> Null] @@ blocker
  /\ UNCHANGED <<fuel, queue, scheduled, mutor, mute>>

Send(cown) ==
  LET senders == CurrentMessage(cown) IN
  /\ running[cown]
  /\ fuel > 0
  /\ \E receivers \in SUBSET Cowns:
    /\ Cardinality(receivers) > 0
    /\ queue' =
      (Min(receivers) :> Append(queue[Min(receivers)], receivers)) @@ queue
    /\ IF \E c \in receivers: priority[c] = 1 THEN
      LET prioritizing == Prioritizing(receivers) IN
      LET unmuting == LowPriority(prioritizing) IN
      /\ priority' = [c \in prioritizing |-> 1] @@ priority
      /\ scheduled' = [c \in unmuting |-> TRUE] @@ scheduled
      /\ LET mutors == {c \in receivers \ senders: ValidMutor(c)} IN
        IF
          /\ mutors /= {}
          /\ mutor[cown] = Null
          /\ \A c \in senders: priority[c] = 0
          /\ \A c \in senders: c \notin receivers \* TODO: justify
        THEN
          /\ mutor' = (cown :> Min(mutors)) @@ mutor
        ELSE
          /\ UNCHANGED <<mutor>>
      ELSE
        /\ UNCHANGED <<scheduled, priority, mutor>>
  /\ fuel' = fuel - 1
  /\ UNCHANGED <<running, blocker, mute>>

Complete(cown) ==
  LET msg == CurrentMessage(cown) IN
  /\ running[cown]
  /\ IF mutor[cown] /= Null THEN
      LET muting == {c \in msg: priority[c] = 0} IN
      /\ priority' = [c \in muting |-> -1] @@ priority
      /\ mute' = (mutor[cown] :> mute[mutor[cown]] \union muting) @@ mute
      /\ scheduled' = [c \in msg |-> c \notin muting] @@ scheduled
    ELSE
      /\ scheduled' = [c \in msg |-> TRUE] @@ scheduled
      /\ UNCHANGED <<priority, mute>>
  /\ queue' = (cown :> Tail(queue[cown])) @@ queue
  /\ running' = (cown :> FALSE) @@ running
  /\ mutor' = (cown :> Null) @@ mutor
  /\ UNCHANGED <<fuel, blocker>>

Unmute ==
  LET invalid_keys == {c \in DOMAIN mute: (priority[c] = 0) \/ Sleeping(c)} IN
  LET unmuting == UNION Range([k \in invalid_keys |-> LowPriority(mute[k])]) IN
  /\ unmuting /= {}
  /\ priority' = [c \in unmuting |-> 0] @@ priority
  /\ mute' = [c \in invalid_keys |-> {}] @@ mute
  /\ scheduled' = [c \in unmuting |-> TRUE] @@ scheduled
  /\ UNCHANGED <<fuel, queue, running, blocker, mutor>>

Run(cown) ==
  \/ Acquire(cown)
  \/ Prerun(cown)
  \/ Send(cown)
  \/ Complete(cown)

Next == Terminating \/ \E c \in Cowns: Run(c) \/ Unmute

Spec ==
  /\ Init
  /\ [][Next]_vars
  /\ \A c \in Cowns: WF_vars(Run(c))
  /\ WF_vars(Unmute)

MessageLimit ==
  LET msgs == ReduceSet(LAMBDA c, sum: sum + Len(queue[c]), Cowns, 0) IN
  msgs <= (BehaviourLimit + Max(Cowns))

RunningIsScheduled ==
  \A c \in Cowns: running[c] => scheduled[c] /\ (c = Max(CurrentMessage(c)))

CownNotMutedBySelf == \A c \in Cowns: c \notin mute[c]

LowPriorityNotScheduled == \A c \in Cowns: (priority[c] = -1) => ~scheduled[c]

LowPriorityMuted == \A c \in Cowns: (priority[c] = -1) => Muted(c)

WillScheduleCown == \E c \in Cowns:
  \/ scheduled[c]
  \/
    /\ priority[c] = -1
    /\ \E k \in DOMAIN mute: (c \in mute[k]) /\ (priority[k] = 0)

BehaviourAcquisition ==
  \A c \in Cowns: scheduled[c] =>
    ~(\E k \in Cowns: (k > c) /\ (c \in UNION Range(queue[k])))

Nonblocking ==
  \A c \in Cowns: \A m \in Range(queue[c]):
    ~(\E h \in HighPriority(m): \E l \in LowPriority(m): (h < c) /\ (l <= c))

RunningNotBlocked ==
  \A c \in Cowns: running[c] => (\A k \in CurrentMessage(c): blocker[k] = Null)

Termination == <>[](\A c \in Cowns: Sleeping(c))

SomeCownWillBeScheduled == []<>(\E c \in Cowns: scheduled[c])

====
