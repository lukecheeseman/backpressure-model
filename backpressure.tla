---- MODULE backpressure ----

EXTENDS FiniteSets, Naturals, Sequences, TLC

(*
Goals:
- Qiuescence is reached
- A message that has acquired an overloaded cown will never be placed on the
  queue of a muted cown
*)

CONSTANTS Null, Normal, Overloaded, Muted
MessageLimit == 3
Cowns == 1..4
Schedulers == 1..3

\* Intersects(a, b) == a \intersect b /= {}
Range(f) == {f[x]: x \in DOMAIN f}
Min(s) == CHOOSE x \in s: \A y \in s \ {x}: y > x
Max(s) == CHOOSE x \in s: \A y \in s \ {x}: y < x
Subsets(s, min, max) ==
  {cs \in SUBSET s: (Cardinality(cs) >= min) /\ (Cardinality(cs) <= max)}
Pick(s) == CHOOSE x \in s: TRUE
ReduceSet(op(_, _), set, acc) ==
  LET f[s \in SUBSET set] ==
    IF s = {} THEN acc ELSE LET x == Pick(s) IN op(x, f[s \ {x}])
  IN f[set]

(* --algorithm backpressure

variables
  message_fuel = MessageLimit,
  queue = [c \in Cowns |-> <<{c}>>],
  acquired = [c \in Cowns |-> FALSE],
  state = [c \in Cowns |-> Normal],

define
  Sleeping(cown)
    == (queue[cown] = <<>>)
    /\ ~acquired[cown]
  Available(cown)
    == (queue[cown] /= <<>>)
    /\ ~acquired[cown]
    /\ (state[cown] /= Muted)
  Quiescent(cowns) == \A c \in cowns: Sleeping(c)
  TriggersMuting(cown) == state[cown] \in {Overloaded, Muted}
  RefCount(cown) ==
    LET RC(q, c) == Cardinality({i \in DOMAIN q: c \in q[i]})
    IN ReduceSet(LAMBDA c, sum: sum + RC(queue[c], cown), Cowns, 0)

  SleepingCownsArentOverloaded ==
    \A c \in Cowns: (Sleeping(c) => state[c] /= Overloaded)
  CownWithZeroRCIsSleeping ==
    \A c \in Cowns: (RefCount(c) = 0 => Sleeping(c))
end define;

fair process scheduler \in Schedulers
variables
  running = Null,
  mute_map = [c \in Cowns |-> {}],
begin
Acquire:
  with
    \* Invalid keys have a zero refcount or no longer trigger muting.
    keys = {c \in Cowns: (RefCount(c) = 0) \/ ~TriggersMuting(c)},
    \* Unmute the muted range of all invalid keys.
    unmuting =
      {c \in UNION Range([k \in keys |-> mute_map[k]]): state[c] = Muted},
  do
    \* Delete entries and unmute.
    mute_map := [k \in keys |-> {}] @@ mute_map;
    state := [c \in unmuting |-> Normal] @@ state;

    await (\E c \in Cowns: Available(c)) \/ Quiescent(Cowns);
    if Quiescent(Cowns) then
      goto Done;
    else
      with c \in {c \in Cowns: Available(c)} do running := c; end with;
      acquired := (running :> TRUE) @@ acquired;
    end if;
  end with;

Run:
  with
    \* Pop the head of its message queue
    msg = Head(queue[running]),
    \* Dequeue msg
    queue_ = (running :> Tail(queue[running])) @@ queue,
  do
    assert running \in msg;
    assert \A c \in msg: acquired[c] \/ (c > running);

    if running < Max(msg) then
      \* Forward message to the next cown.
      with next = Min({c \in msg: c > running}) do
        queue := (next :> Append(queue[next], msg)) @@ queue_;
      end with;
    else
      with
        \* Any acquired cown with more messages in its queue may toggle their
        \* state to overloaded. Acquired cowns with an empty queue will become
        \* normal.
        overload \in SUBSET {c \in msg: queue_[c] /= <<>>},
        state_ =
          [c \in overload |-> Overloaded] @@ [c \in msg |-> Normal] @@ state,
      do
        \* Maybe create a new behaviour
        if message_fuel > 0 then
          either
            with new_msg \in Subsets(Cowns, 1, 3), next = Min(new_msg) do
              queue := (next :> Append(queue_[next], new_msg)) @@ queue_;
              \* Mute if receiver triggers muting
              if TriggersMuting(next)
                /\ (running \notin new_msg)
                /\ (state[running] /= Overloaded)
              then
                state := (running :> Muted) @@ state_;
                mute_map :=
                  (next :> mute_map[next] \union {running}) @@ mute_map;
              else
                state := state_;
              end if;
            end with;
            message_fuel := message_fuel - 1;
          or
            queue := queue_;
            state := state_;
          end either;
        else
          queue := queue_;
          state := state_;
        end if;
      end with;
      \* Release any acquired cowns from this behaviour.
      acquired := [c \in msg |-> FALSE] @@ acquired;
    end if;

    running := Null;
    goto Acquire;
  end with;
end process;

end algorithm; *)

Completion == (\A sched \in Schedulers: pc[sched] = "Done") => Quiescent(Cowns)
MutedCownNotRunning ==
  \A c \in Range(running): (c = Null) \/ (state[c] /= Muted)

====
