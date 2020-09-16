---- MODULE backpressure ----

EXTENDS FiniteSets, Naturals, TLC

Cowns == 1..3
Behaviours == 1..3

(* --algorithm backpressure

variables
  \* Behaviours that are still waiting to run
  pending = [b \in Behaviours |-> {}],
  \* Cowns available for running behaviours
  available = Cowns,
  \* Cowns that are unavailable
  unavailable = {},
  \* Cowns that are overloaded
  overloaded = {},
  \* Mapping of mutor to unavailable
  mute_map = [c \in Cowns |-> {}],

define
  \* unavailable cowns must not be available, overloaded, or protected.
  UnavailableInv == (unavailable \intersect (available \union overloaded)) = {}
  \* All unavailable cowns must exist in at least one mute map entry.
  MuteMapInv == \A m \in unavailable : \E c \in Cowns : m \in mute_map[c]
  \* This does not hold
  ReverseInv == \A c \in Cowns: mute_map[c] \subseteq unavailable

  \* All invalid mute map entries will eventually be removed.
  MuteMapProp ==
    []<>(\A k \in DOMAIN mute_map: mute_map[k] = {} \/ k \in overloaded)
end define;

fair process behaviour \in Behaviours
variables
  cowns \in SUBSET Cowns,
begin
Create:
  \* Create a behaviour that requires cowns
  pending[self] := cowns;

Acquire:
  \* Acquire the cowns
  await (cowns \subseteq available) \/
        (\E c \in cowns: c \in overloaded /\ cowns \subseteq (available \union unavailable));
  unavailable := unavailable \ cowns;
  available := available \ cowns;
  
  \* Remove the pending entry
  pending[self] := {};

Action:
  \* Any cowns cown may toggle their overloaded state when the behaviour completes.
  with overload \in SUBSET cowns,
       unoverload \in SUBSET ((cowns \ overload) \intersect overloaded),
       unmute = UNION {mute_map[c] : c \in unoverload}
  do
    overloaded := (overloaded \ unoverload) \union overload;
  
    with receiver \in Cowns, mute = {c \in cowns: c \notin overloaded} do
      \* Mute senders if the receiver triggers muting and the receiver isn't one of the senders.
      if receiver \in {c \in Cowns: (\E b \in Behaviours: c \in pending[b]) /\ c \in ((overloaded \union unavailable) \ cowns)} then
        \* Add muted senders to the mute map entry for the receiver.
        unavailable := (unavailable \union mute) \ unmute;
        available := available \union (cowns \ mute) \union unmute;
        mute_map := (receiver :> mute_map[receiver] \union mute) @@ [m \in unoverload |-> {} ] @@ mute_map;
      else      
        \* Senders are not muted, so all become available.
        unavailable := unavailable \ unmute;
        available := available \union cowns \union unmute;
        mute_map := [m \in unoverload |-> {} ] @@ mute_map;
      end if;
    end with;
  end with;
end process;

end algorithm; *)
\* BEGIN TRANSLATION - the hash of the PCal code: PCal-5c36600a11111e425a922962e903ef5c
VARIABLES pending, available, unavailable, overloaded, mute_map, pc

(* define statement *)
UnavailableInv == (unavailable \intersect (available \union overloaded)) = {}

MuteMapInv == \A m \in unavailable : \E c \in Cowns : m \in mute_map[c]

ReverseInv == \A c \in Cowns: mute_map[c] \subseteq unavailable


MuteMapProp ==
  []<>(\A k \in DOMAIN mute_map: mute_map[k] = {} \/ k \in overloaded)

VARIABLE cowns

vars == << pending, available, unavailable, overloaded, mute_map, pc, cowns
        >>

ProcSet == (Behaviours)

Init == (* Global variables *)
        /\ pending = [b \in Behaviours |-> {}]
        /\ available = Cowns
        /\ unavailable = {}
        /\ overloaded = {}
        /\ mute_map = [c \in Cowns |-> {}]
        (* Process behaviour *)
        /\ cowns \in [Behaviours -> SUBSET Cowns]
        /\ pc = [self \in ProcSet |-> "Create"]

Create(self) == /\ pc[self] = "Create"
                /\ pending' = [pending EXCEPT ![self] = cowns[self]]
                /\ pc' = [pc EXCEPT ![self] = "Acquire"]
                /\ UNCHANGED << available, unavailable, overloaded, mute_map, 
                                cowns >>

Acquire(self) == /\ pc[self] = "Acquire"
                 /\ (cowns[self] \subseteq available) \/
                    (\E c \in cowns[self]: c \in overloaded /\ cowns[self] \subseteq (available \union unavailable))
                 /\ unavailable' = unavailable \ cowns[self]
                 /\ available' = available \ cowns[self]
                 /\ pending' = [pending EXCEPT ![self] = {}]
                 /\ pc' = [pc EXCEPT ![self] = "Action"]
                 /\ UNCHANGED << overloaded, mute_map, cowns >>

Action(self) == /\ pc[self] = "Action"
                /\ \E overload \in SUBSET cowns[self]:
                     \E unoverload \in SUBSET ((cowns[self] \ overload) \intersect overloaded):
                       LET unmute == UNION {mute_map[c] : c \in unoverload} IN
                         /\ overloaded' = ((overloaded \ unoverload) \union overload)
                         /\ \E receiver \in Cowns:
                              LET mute == {c \in cowns[self]: c \notin overloaded'} IN
                                IF receiver \in {c \in Cowns: (\E b \in Behaviours: c \in pending[b]) /\ c \in ((overloaded' \union unavailable) \ cowns[self])}
                                   THEN /\ unavailable' = (unavailable \union mute) \ unmute
                                        /\ available' = (available \union (cowns[self] \ mute) \union unmute)
                                        /\ mute_map' = (receiver :> mute_map[receiver] \union mute) @@ [m \in unoverload |-> {} ] @@ mute_map
                                   ELSE /\ unavailable' = unavailable \ unmute
                                        /\ available' = (available \union cowns[self] \union unmute)
                                        /\ mute_map' = [m \in unoverload |-> {} ] @@ mute_map
                /\ pc' = [pc EXCEPT ![self] = "Done"]
                /\ UNCHANGED << pending, cowns >>

behaviour(self) == Create(self) \/ Acquire(self) \/ Action(self)

(* Allow infinite stuttering to prevent deadlock on termination. *)
Terminating == /\ \A self \in ProcSet: pc[self] = "Done"
               /\ UNCHANGED vars

Next == (\E self \in Behaviours: behaviour(self))
           \/ Terminating

Spec == /\ Init /\ [][Next]_vars
        /\ \A self \in Behaviours : WF_vars(behaviour(self))

Termination == <>(\A self \in ProcSet: pc[self] = "Done")

\* END TRANSLATION - the hash of the generated TLA code (remove to silence divergence warnings): TLA-fcee8c8ccf6983438bf088dad6a81223

====

(* TODO in `RunStep`:

The contition `(next \in unavailable) /\ (\E c \in required: HasPriority(c))` is used
to ensure that unavailable cowns never indefinetly prevent a behaviour, scheduled on an
overloaded cown, from running. Removing this condition from the `await` will
result in the `Termination` property failing. The `Termination` property is used
to check that all behaviours eventually run to completion.

One of the following should be done:
  1. The model should be modified to support `Termination` in a way that can be
     implemented without unacceptable overhead.

  2. The `Termination` property should be replaced by a weaker property, or
     there should be another way to model that unavailable cowns are eventually
     ununavailable. The property implemented in Verona currently is that any
     behaviour requiring a cown that is overloaded on creation of the behaviour
     will not prevent the behaviour from running. So the following example
     remains an issue:
      ```
      Cown 1 is unavailable. Behaviour `a` requires {2}. Behaviour `b` requires {1,2}.
      - `b`: `Protect`: 1 and 2 have no priority, nothing is protected.
      - `a`: `Action`: overload 2.
      - `b`: `AcquireNext`: await 1 becoming available, but 1 is unavailable.
      ```

*)
