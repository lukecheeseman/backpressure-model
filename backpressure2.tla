---- MODULE backpressure2 ----

(* run with:
pcal backpressure2.tla && \
  TLC_JAVA_OPTS="-XX:+UseParallelGC" tlc backpressure2.tla -workers $(nproc)
*)

EXTENDS FiniteSets, Naturals, TLC

CONSTANT null
Cowns == 1..3
Behaviours == 1..3

Range(f) == {f[x] : x \in DOMAIN f}
Min(s) == CHOOSE x \in s: \A y \in s: x <= y
Intersects(a, b) == a \intersect b /= {}
Subsets(s, min, max) ==
  {cs \in SUBSET s: (Cardinality(cs) >= min) /\ (Cardinality(cs) <= max)}

(* --algorithm backpressure

\* TODO: document variables
variables
  Available = Cowns,
  \* TODO: compensate for few behaviours with initial overloaded set
  \* Overloaded \in SUBSET Cowns,
  Overloaded = {},
  Muted = {},
  Protected = {},
  MuteMap = [c \in Cowns |-> {}],
  \* RefCount must be tracked manually due to limitations of accessing the
  \* global process variables from PlusCal
  RefCount = [c \in Cowns |-> 0],
  BehavioursUnaccounted = Cardinality(Behaviours),

define
  \* Normal == Cowns \ UNION {Overloaded, Muted, Protected}
  RC(cown) == IF BehavioursUnaccounted = 0 THEN RefCount[cown] ELSE 2
  TriggersMute(cown)
    == (RC(cown) > 0) /\ ((cown \in Overloaded) \/ (cown \in Muted))
  TriggersUnmute(cown)
    == (RC(cown) = 0) \/ (cown \notin Overloaded)
end define

fair process behaviour \in Behaviours
variables
  receivers \in Subsets(Cowns, 0, 3),
  acquired = {},
begin
Create:
  \* incref receivers
  RefCount := [r \in receivers |-> RefCount[r] + 1] @@ RefCount;
  BehavioursUnaccounted := BehavioursUnaccounted - 1;

  \* TODO: empty receivers, does this improve check time?
  if receivers = {} then goto Done; end if;

Acquire:
  while acquired /= receivers do
Protect:
    with remaining = receivers \ acquired do
      \* Protected or overloaded receivers will protect all other receivers.
      if Intersects(receivers, Overloaded \union Protected) then
        Protected := Protected \union remaining;
        \* Unmute any receivers that were previously muted.
        Muted := Muted \ remaining;
        Available := Available \union remaining;
      end if;
    end with;
AcquireInner:
    with next = Min(receivers \ acquired) do
      \* Wait for the next receiver to be available.
      await next \in Available;
      \* Acquire the next receiver.
      acquired := acquired \union {next};
      \* Prevent other behaviours from acquiring this receiver by making it
      \* unavailable.
      Available := Available \ {next};
    end with;
  end while;

Run:
  assert acquired = receivers;
  assert \A r \in receivers: RC(r) > 0;
  assert ~Intersects(receivers, Muted);
  \* Any receiver may toggle their overloaded state.
  with overload \in SUBSET receivers do
    Overloaded := (Overloaded \ receivers) \union overload;
  end with;
  \* Identify a possible recipient for a new behaviour created by this
  \* behaviour. The receivers of this behaviour will not be muted if the
  \* recipient is the empty set, or if the recipient is in the set of receivers.
  with recipient \in Subsets(Cowns, 0, 1) do
    if (recipient /= {})
      /\ ~Intersects(recipient, receivers)
      /\ TriggersMute(CHOOSE r \in recipient : TRUE)
    then
      with muted = {r \in receivers: r \notin (Overloaded \union Protected)} do
        Muted := Muted \union muted;
        \* Add these muted cowns to the MuteMap entry corresponting to this
        \* recipient.
        MuteMap := [m \in recipient |-> MuteMap[m] \union muted] @@ MuteMap;
        \* Make other receivers available for other behaviours.
        Available := Available \union (receivers \ muted);
      end with;
    else
      \* Nothing is muted. Make all receivers available for other behaviours.
      Available := Available \union receivers;
    end if;
  end with;
  \* Empty acquired set (useful for debugging).
  acquired := {};
  \* Decref receivers.
  RefCount := [r \in receivers |-> RefCount[r] - 1] @@ RefCount;

Unmute:
  await BehavioursUnaccounted = 0;

  with unmuting =
    UNION Range([c \in {k \in Cowns : TriggersUnmute(k)} |-> MuteMap[c]])
  do
    MuteMap := [c \in unmuting |-> {}] @@ MuteMap;
    Muted := Muted \ unmuting;
    Available := Available \union unmuting;
  end with;

end process;

end algorithm; *)

\* BEGIN TRANSLATION - the hash of the PCal code: PCal-18a0131aa1cb3bf2aab35b25ef768479
VARIABLES Available, Overloaded, Muted, Protected, MuteMap, RefCount, 
          BehavioursUnaccounted, pc

(* define statement *)
RC(cown) == IF BehavioursUnaccounted = 0 THEN RefCount[cown] ELSE 2
TriggersMute(cown)
  == (RC(cown) > 0) /\ ((cown \in Overloaded) \/ (cown \in Muted))
TriggersUnmute(cown)
  == (RC(cown) = 0) \/ (cown \notin Overloaded)

VARIABLES receivers, acquired

vars == << Available, Overloaded, Muted, Protected, MuteMap, RefCount, 
           BehavioursUnaccounted, pc, receivers, acquired >>

ProcSet == (Behaviours)

Init == (* Global variables *)
        /\ Available = Cowns
        /\ Overloaded = {}
        /\ Muted = {}
        /\ Protected = {}
        /\ MuteMap = [c \in Cowns |-> {}]
        /\ RefCount = [c \in Cowns |-> 0]
        /\ BehavioursUnaccounted = Cardinality(Behaviours)
        (* Process behaviour *)
        /\ receivers \in [Behaviours -> Subsets(Cowns, 0, 3)]
        /\ acquired = [self \in Behaviours |-> {}]
        /\ pc = [self \in ProcSet |-> "Create"]

Create(self) == /\ pc[self] = "Create"
                /\ RefCount' = [r \in receivers[self] |-> RefCount[r] + 1] @@ RefCount
                /\ BehavioursUnaccounted' = BehavioursUnaccounted - 1
                /\ IF receivers[self] = {}
                      THEN /\ pc' = [pc EXCEPT ![self] = "Done"]
                      ELSE /\ pc' = [pc EXCEPT ![self] = "Acquire"]
                /\ UNCHANGED << Available, Overloaded, Muted, Protected, 
                                MuteMap, receivers, acquired >>

Acquire(self) == /\ pc[self] = "Acquire"
                 /\ IF acquired[self] /= receivers[self]
                       THEN /\ pc' = [pc EXCEPT ![self] = "Protect"]
                       ELSE /\ pc' = [pc EXCEPT ![self] = "Run"]
                 /\ UNCHANGED << Available, Overloaded, Muted, Protected, 
                                 MuteMap, RefCount, BehavioursUnaccounted, 
                                 receivers, acquired >>

Protect(self) == /\ pc[self] = "Protect"
                 /\ LET remaining == receivers[self] \ acquired[self] IN
                      IF Intersects(receivers[self], Overloaded \union Protected)
                         THEN /\ Protected' = (Protected \union remaining)
                              /\ Muted' = Muted \ remaining
                              /\ Available' = (Available \union remaining)
                         ELSE /\ TRUE
                              /\ UNCHANGED << Available, Muted, Protected >>
                 /\ pc' = [pc EXCEPT ![self] = "AcquireInner"]
                 /\ UNCHANGED << Overloaded, MuteMap, RefCount, 
                                 BehavioursUnaccounted, receivers, acquired >>

AcquireInner(self) == /\ pc[self] = "AcquireInner"
                      /\ LET next == Min(receivers[self] \ acquired[self]) IN
                           /\ next \in Available
                           /\ acquired' = [acquired EXCEPT ![self] = acquired[self] \union {next}]
                           /\ Available' = Available \ {next}
                      /\ pc' = [pc EXCEPT ![self] = "Acquire"]
                      /\ UNCHANGED << Overloaded, Muted, Protected, MuteMap, 
                                      RefCount, BehavioursUnaccounted, 
                                      receivers >>

Run(self) == /\ pc[self] = "Run"
             /\ Assert(acquired[self] = receivers[self], 
                       "Failure of assertion at line 83, column 3.")
             /\ Assert(\A r \in receivers[self]: RC(r) > 0, 
                       "Failure of assertion at line 84, column 3.")
             /\ Assert(~Intersects(receivers[self], Muted), 
                       "Failure of assertion at line 85, column 3.")
             /\ \E overload \in SUBSET receivers[self]:
                  Overloaded' = ((Overloaded \ receivers[self]) \union overload)
             /\ \E recipient \in Subsets(Cowns, 0, 1):
                  IF  (recipient /= {})
                     /\ ~Intersects(recipient, receivers[self])
                     /\ TriggersMute(CHOOSE r \in recipient : TRUE)
                     THEN /\ LET muted == {r \in receivers[self]: r \notin (Overloaded' \union Protected)} IN
                               /\ Muted' = (Muted \union muted)
                               /\ MuteMap' = [m \in recipient |-> MuteMap[m] \union muted] @@ MuteMap
                               /\ Available' = (Available \union (receivers[self] \ muted))
                     ELSE /\ Available' = (Available \union receivers[self])
                          /\ UNCHANGED << Muted, MuteMap >>
             /\ acquired' = [acquired EXCEPT ![self] = {}]
             /\ RefCount' = [r \in receivers[self] |-> RefCount[r] - 1] @@ RefCount
             /\ pc' = [pc EXCEPT ![self] = "Unmute"]
             /\ UNCHANGED << Protected, BehavioursUnaccounted, receivers >>

Unmute(self) == /\ pc[self] = "Unmute"
                /\ BehavioursUnaccounted = 0
                /\ LET unmuting == UNION Range([c \in {k \in Cowns : TriggersUnmute(k)} |-> MuteMap[c]]) IN
                     /\ MuteMap' = [c \in unmuting |-> {}] @@ MuteMap
                     /\ Muted' = Muted \ unmuting
                     /\ Available' = (Available \union unmuting)
                /\ pc' = [pc EXCEPT ![self] = "Done"]
                /\ UNCHANGED << Overloaded, Protected, RefCount, 
                                BehavioursUnaccounted, receivers, acquired >>

behaviour(self) == Create(self) \/ Acquire(self) \/ Protect(self)
                      \/ AcquireInner(self) \/ Run(self) \/ Unmute(self)

(* Allow infinite stuttering to prevent deadlock on termination. *)
Terminating == /\ \A self \in ProcSet: pc[self] = "Done"
               /\ UNCHANGED vars

Next == (\E self \in Behaviours: behaviour(self))
           \/ Terminating

Spec == /\ Init /\ [][Next]_vars
        /\ \A self \in Behaviours : WF_vars(behaviour(self))

Termination == <>(\A self \in ProcSet: pc[self] = "Done")

\* END TRANSLATION - the hash of the generated TLA code (remove to silence divergence warnings): TLA-ca89eef553a6f3f86955d75678034dc1

MutedInv == ~Intersects(Muted, UNION {Protected, Overloaded, Available})
RCDrops == (\A b \in Behaviours: pc[b] = "Done") => (\A c \in Cowns: RC(c) = 0)
\* OverloadedNotZeroRC == \A c \in Cowns : ~Overloaded[c] \/ (RC(c) > 0)

====
