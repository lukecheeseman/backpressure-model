---- MODULE backpressure ----

EXTENDS FiniteSets, Naturals, Sequences, TLC

CONSTANTS Null, Normal, Overloaded
MessageLimit == 5
Cowns == 1..5
Schedulers == 1..3

\* Range(f) == {f[x]: x \in DOMAIN f}
\* Intersects(a, b) == a \intersect b /= {}
Min(s) == CHOOSE x \in s: \A y \in s \ {x}: y > x
Max(s) == CHOOSE x \in s: \A y \in s \ {x}: y < x
Subsets(s, min, max) ==
  {cs \in SUBSET s: (Cardinality(cs) >= min) /\ (Cardinality(cs) <= max)}

(* --algorithm backpressure

variables
  message_fuel = MessageLimit,
  initial_msg \in {cowns \in Subsets(Cowns, 1, 3): TRUE},
  queue = (Min(initial_msg) :> <<initial_msg>>) @@ [c \in Cowns |-> <<>>],
  acquired = [c \in Cowns |-> FALSE],
  state = [c \in Cowns |-> Normal]

define
  Sleeping(cown) == (queue[cown] = <<>>) /\ ~acquired[cown]
  Available(cown) == (queue[cown] /= <<>>) /\ ~acquired[cown]
  Quiescent(cowns) == \A c \in cowns: Sleeping(c)

  SleepingCownsAreNormal == \A c \in Cowns: (Sleeping(c) => state[c] = Normal)
end define;

fair process scheduler \in Schedulers
variables running = Null
begin
Acquire:
  await (\E c \in Cowns: Available(c)) \/ Quiescent(Cowns);
  if Quiescent(Cowns) then
    goto Done;
  else
    with c \in {c \in Cowns: Available(c)} do running := c; end with;
    acquired := (running :> TRUE) @@ acquired;
  end if;
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
      \* Maybe create a new behaviour
      if message_fuel > 0 then
        either
          with new_msg \in Subsets(Cowns, 1, 3), next = Min(new_msg) do
            queue := (next :> Append(queue_[next], new_msg)) @@ queue_;
          end with;
          message_fuel := message_fuel - 1;
        or queue := queue_;
        end either;
      else queue := queue_;
      end if;
      \* Any acquired cown with more messages in its queue may toggle their
      \* state to overloaded. Acquired cowns with an empty queue will become
      \* normal.
      with overload \in SUBSET {c \in msg: queue_[c] /= <<>>} do
        state :=
          [c \in overload |-> Overloaded] @@ [c \in msg |-> Normal] @@ state;
      end with;
      \* TODO: mute
      \* Release any acquired cowns from this behaviour.
      acquired := [c \in msg |-> FALSE] @@ acquired;
    end if;

    running := Null;
    goto Acquire;
  end with;
end process;

end algorithm; *)

Completion == (\A sched \in Schedulers: pc[sched] = "Done") => Quiescent(Cowns)

====
