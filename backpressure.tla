---- MODULE backpressure ----

EXTENDS FiniteSets, Naturals, Sequences, TLC

(*
Goals:
- Quiescence is reached
- A message that has acquired an overloaded cown will never be placed on the
  queue of a muted cown
*)

CONSTANTS Null, Normal, Overloaded, Muted
MessageLimit == 3
Cowns == 1..3 \* TODO: 1..4
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
  protected = [c \in Cowns |-> FALSE],
  next_acq = [c \in Cowns |-> Null],

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
  HasPriority(cown) == (state[cown] = Overloaded) \/ protected[cown]
  Dequeue(cown) == (cown :> Tail(queue[cown])) @@ queue
  Send(cown, msg, q) == (cown :> Append(q[cown], msg)) @@ q
  Unmute(cowns, st) == [c \in {c \in cowns: st[c] = Muted} |-> Normal] @@ st
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
Prerun:
  if Quiescent(Cowns) then
    \* Shutdown
    goto Done;
  elsif \E c \in Cowns: Available(c) then
    \* Acquire an available cown
    with c \in {c \in Cowns: Available(c)} do running := c; end with;
    acquired := (running :> TRUE) @@ acquired;
  else
    \* Scan mute map.
    with
      \* Invalid keys have a zero refcount or no longer trigger muting.
      keys = {c \in Cowns: (RefCount(c) = 0) \/ ~TriggersMuting(c)},
      \* Unmute the muted range of all invalid keys.
      unmuting =
        {c \in UNION Range([k \in keys |-> mute_map[k]]): state[c] = Muted},
    do
      state := Unmute(unmuting, state);
      mute_map := [k \in keys |-> {}] @@ mute_map;
      goto Prerun;
    end with;
  end if;

Run:
  with
    \* Pop the head of its message queue
    msg = Head(queue[running]),
  do
    assert running \in msg;
    assert \A c \in msg: acquired[c] \/ (c > running);

    if running < Max(msg) then
      \* Forward message to the next cown.
      with next = Min({c \in msg: c > running}) do
        queue := Send(next, msg, Dequeue(running));
        next_acq := (running :> next) @@ next_acq;
      end with;
      \* Protect receivers if any have priority.
      if \E c \in msg: HasPriority(c) then
        state := Unmute(msg, state);
        protected := [c \in msg |-> TRUE] @@ protected;
      end if;
    else
      \* Any acquired cown with more messages in its queue may toggle to
      \* overloaded. Acquired cowns with an empty queue will become normal.

      \* Maybe create a new behaviour
      either
        \* Disable this branch if zero fuel
        await message_fuel > 0;
        with
          queue_ = Dequeue(running),
          overloading \in SUBSET {c \in msg: queue_[c] /= <<>>},
          state_ =
            [c \in overloading |-> Overloaded] @@
            [c \in msg |-> Normal] @@ state,
          \* mutable = {c \in cown: ~HasPriority(c) /\ (c \in overloading)},

          new_msg \in Subsets(Cowns, 1, 3),
          next = Min(new_msg),
          protect = \E c \in new_msg: HasPriority(c),
          state__ = IF protect THEN Unmute(new_msg, state_) ELSE state_,
        do
          queue := Send(next, new_msg, Dequeue(running));
          \* Protect receivers if any have priority.
          if protect then
            protected := [c \in new_msg |-> TRUE] @@ protected;
          end if;
          \* Mute if receiver triggers muting and running cowns are mutable
          if TriggersMuting(next)
            /\ (running \notin new_msg)
            /\ ~HasPriority(running)
          then
            state := (running :> Muted) @@ state__;
            mute_map :=
              (next :> mute_map[next] \union {running}) @@ mute_map;
          else
            state := state__;
          end if;
        end with;
        message_fuel := message_fuel - 1;
      or
        queue := Dequeue(running);
        with overloading \in SUBSET {c \in msg: queue[c] /= <<>>} do
          state :=
            [c \in overloading |-> Overloaded] @@
            [c \in msg |-> Normal] @@ state;
        end with;
      end either;
      next_acq := (running :> Null) @@ next_acq;
      \* Release any acquired cowns from this behaviour.
      acquired := [c \in msg |-> FALSE] @@ acquired;
    end if;

    running := Null;
    goto Prerun;
  end with;
end process;

end algorithm; *)

Completion == (\A sched \in Schedulers: pc[sched] = "Done") => Quiescent(Cowns)
MutedCownNotRunning ==
  \A c \in Range(running): (c = Null) \/ (state[c] /= Muted)

====
