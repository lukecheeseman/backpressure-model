---- MODULE backpressure ----

EXTENDS FiniteSets, Naturals, Sequences, TLC

MessageLimit == 5
Cowns == 1..5
Schedulers == 1..3

\* Range(f) == {f[x]: x \in DOMAIN f}
\* Min(s) == CHOOSE x \in s: \A y \in s \ {x}: y > x
\* Intersects(a, b) == a \intersect b /= {}
Subsets(s, min, max) ==
  {cs \in SUBSET s: (Cardinality(cs) >= min) /\ (Cardinality(cs) <= max)}

(* --algorithm backpressure

variables
  message_limit = MessageLimit,
  initial_msg \in {cowns \in Subsets(Cowns, 1, 3): TRUE},
  acquired = [c \in Cowns |-> FALSE],
  queue = (1 :> <<initial_msg>>) @@ [c \in Cowns |-> <<>>],

define
  Available(cown) == ~acquired[cown] /\ (queue[cown] /= <<>>)
  Sleeping(cown) == ~acquired[cown] /\ (queue[cown] = <<>>)
  Quiescent(cowns) == \A c \in cowns: Sleeping(c)
end define;

fair process scheduler \in Schedulers
begin
Run:
await (\E c \in Cowns: Available(c)) \/ Quiescent(Cowns);
if Quiescent(Cowns) then goto Done;
else with
  \* Select an available cown
  running \in {c \in Cowns: Available(c)},
  \* Pop the head of its message queue
  msg = Head(queue[running]),
do
  \* Dequeue msg
  queue := (running :> Tail(queue[running])) @@ queue;

  goto Run;
end with;
end if;

end process;

end algorithm; *)

====
