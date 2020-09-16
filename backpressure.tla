---- MODULE backpressure ----

EXTENDS FiniteSets, Naturals, TLC

Cowns == 1..3
Behaviours == 1..3

Unwrap(s) == CHOOSE x \in s: Cardinality(s) = 1
Range(f) == {f[x]: x \in DOMAIN f}
Min(s) == CHOOSE x \in s: \A y \in s \ {x}: y > x
Intersects(a, b) == a \intersect b /= {}
Subsets(s, min, max) ==
  {cs \in SUBSET s: (Cardinality(cs) >= min) /\ (Cardinality(cs) <= max)}

xor(a, b) == (a \/ b) /\ ~(a /\ b)

(* --algorithm backpressure

variables
  pending = [ b \in Behaviours |-> CHOOSE cs \in SUBSET Cowns: TRUE],
  
  running = {},

  \* Cowns available for running behaviours
  available = Cowns,
  \* Cowns that are unavailable
  unavailable = {},
  \* Cowns that are overloaded
  overloaded = {},
  \* Mapping of mutor to unavailable
  mute_map = [c \in Cowns |-> {}],
  \* Count of behaviours that have yet to run on each cown
  refcount = [c \in Cowns |-> 0],
  \* Count of behaviours with untracked refcounts
  untracked_behaviours = Cardinality(Behaviours),

define
  \* unavailable cowns must not be available, overloaded, or protected.
  UnavailableInv == ~Intersects(unavailable, UNION {available, overloaded})
  \* All unavailable cowns must exist in at least one mute map entry.
  MuteMapInv == \A m \in unavailable: m \in UNION Range(mute_map)
  
  \* This does not hold
  ReverseInv == \A m \in UNION Range(mute_map): m \in unavailable
  
  \* Refcounts must not drop below 0.
  RefcountInv == \A c \in Cowns: refcount[c] >= 0
  \* All refcounts must eventually drop to 0.
  RefcountDropInv ==
    (\A b \in Behaviours: pc[b] = "Done") => (\A c \in Cowns: refcount[c] = 0)

  \* All invalid mute map entries will eventually be removed.
  MuteMapProp ==
    []<>(\A k \in DOMAIN mute_map: mute_map[k] = {} \/ k \in overloaded)

  \* Sending to receiver should mute senders.
  TriggersMuting(receiver) == receiver \in (overloaded \union unavailable)
  \* Cown cannot be unavailable.
  HasPriority(cown) == cown \in overloaded
  
  \* Overloaded(cown) == refcount[c] > threshold
  \* Protected(cown) == \E b \in Behaviours : cown \in required[b] \*c \in Cowns: cown \in behaviours[b] /\ c \in behaviours[b] /\ Overloaded(c)
end define;

fair process behaviour \in Behaviours
variables
  cowns \in Subsets(Cowns, 0, 3),
begin
Create:
  \* Add a refcount to all required cowns.
  refcount := [c \in cowns |-> refcount[c] + 1] @@ refcount;
  \* Indicate that the refcounts for this behaviour have been tracked.
  untracked_behaviours := untracked_behaviours - 1;
  \* Empty required set used to represent fewer behaviours in the system.
  if cowns = {} then goto Done; end if;

RCBarrier:
  \* Wait for refcounts to be valid.
  await untracked_behaviours = 0;

Acquire:
  await (cowns \subseteq available) \/
        (\E c \in cowns: c \in overloaded /\ cowns \subseteq (available \union unavailable));
  unavailable := unavailable \ cowns;
  available := available \ cowns;

Action:
  assert \A c \in cowns: refcount[c] > 0;

  \* Any cowns cown may toggle their overloaded state when the behaviour completes.
  with overload \in SUBSET cowns,
       unoverload \in SUBSET (cowns \ overload),
       unmute = {c \in Cowns : c \in unavailable /\ ~(\E u \in (DOMAIN mute_map \ unoverload) : c \in mute_map[u])} \* pick those we muted that are not in anybody elses mute set
  do 
    overloaded := (overloaded \ unoverload) \union overload;
  
    \* Mute senders if the receiver triggers muting and the receiver isn't one
    \* of the senders.
    with candidates = {c \in Cowns: c \notin cowns /\ TriggersMuting(c)} do
      if candidates /= {} then
        with receiver \in candidates, muting = {c \in cowns: c \notin overloaded} do
          unavailable := (unavailable \union muting) \ unmute;
          \* Add unavailable senders to the mute map entry for the receiver.
          mute_map := ((receiver :> mute_map[receiver] \union muting) @@ mute_map); \* \ unmute;
          available := available \union (cowns \ muting) \union unmute;
        end with;
      else      
        \* Senders are not unavailable, so all become available.
        unavailable := unavailable \ unmute;
        available := available \union cowns \union unmute;
        mute_map := [m \in unmute |-> {} ] @@ mute_map;
      end if;
    end with;
  end with;

  \* Decrement the refcounts of all cowns cowns.
  refcount := [c \in cowns |-> refcount[c] - 1] @@ refcount;
end process;

end algorithm; *)
\* BEGIN TRANSLATION - the hash of the PCal code: PCal-8e5e16fc940552430f5bb9baea4de992
VARIABLES pending, running, available, unavailable, overloaded, mute_map, 
          refcount, untracked_behaviours, pc

(* define statement *)
UnavailableInv == ~Intersects(unavailable, UNION {available, overloaded})

MuteMapInv == \A m \in unavailable: m \in UNION Range(mute_map)


ReverseInv == \A m \in UNION Range(mute_map): m \in unavailable


RefcountInv == \A c \in Cowns: refcount[c] >= 0

RefcountDropInv ==
  (\A b \in Behaviours: pc[b] = "Done") => (\A c \in Cowns: refcount[c] = 0)


MuteMapProp ==
  []<>(\A k \in DOMAIN mute_map: mute_map[k] = {} \/ k \in overloaded)


TriggersMuting(receiver) == receiver \in (overloaded \union unavailable)

HasPriority(cown) == cown \in overloaded

VARIABLE cowns

vars == << pending, running, available, unavailable, overloaded, mute_map, 
           refcount, untracked_behaviours, pc, cowns >>

ProcSet == (Behaviours)

Init == (* Global variables *)
        /\ pending = [ b \in Behaviours |-> CHOOSE cs \in SUBSET Cowns: TRUE]
        /\ running = {}
        /\ available = Cowns
        /\ unavailable = {}
        /\ overloaded = {}
        /\ mute_map = [c \in Cowns |-> {}]
        /\ refcount = [c \in Cowns |-> 0]
        /\ untracked_behaviours = Cardinality(Behaviours)
        (* Process behaviour *)
        /\ cowns \in [Behaviours -> Subsets(Cowns, 0, 3)]
        /\ pc = [self \in ProcSet |-> "Create"]

Create(self) == /\ pc[self] = "Create"
                /\ refcount' = [c \in cowns[self] |-> refcount[c] + 1] @@ refcount
                /\ untracked_behaviours' = untracked_behaviours - 1
                /\ IF cowns[self] = {}
                      THEN /\ pc' = [pc EXCEPT ![self] = "Done"]
                      ELSE /\ pc' = [pc EXCEPT ![self] = "RCBarrier"]
                /\ UNCHANGED << pending, running, available, unavailable, 
                                overloaded, mute_map, cowns >>

RCBarrier(self) == /\ pc[self] = "RCBarrier"
                   /\ untracked_behaviours = 0
                   /\ pc' = [pc EXCEPT ![self] = "Acquire"]
                   /\ UNCHANGED << pending, running, available, unavailable, 
                                   overloaded, mute_map, refcount, 
                                   untracked_behaviours, cowns >>

Acquire(self) == /\ pc[self] = "Acquire"
                 /\ (cowns[self] \subseteq available) \/
                    (\E c \in cowns[self]: c \in overloaded /\ cowns[self] \subseteq (available \union unavailable))
                 /\ unavailable' = unavailable \ cowns[self]
                 /\ available' = available \ cowns[self]
                 /\ pc' = [pc EXCEPT ![self] = "Action"]
                 /\ UNCHANGED << pending, running, overloaded, mute_map, 
                                 refcount, untracked_behaviours, cowns >>

Action(self) == /\ pc[self] = "Action"
                /\ Assert(\A c \in cowns[self]: refcount[c] > 0, 
                          "Failure of assertion at line 88, column 3.")
                /\ \E overload \in SUBSET cowns[self]:
                     \E unoverload \in SUBSET (cowns[self] \ overload):
                       LET unmute == {c \in Cowns : c \in unavailable /\ ~(\E u \in (DOMAIN mute_map \ unoverload) : c \in mute_map[u])} IN
                         /\ overloaded' = ((overloaded \ unoverload) \union overload)
                         /\ LET candidates == {c \in Cowns: c \notin cowns[self] /\ TriggersMuting(c)} IN
                              IF candidates /= {}
                                 THEN /\ \E receiver \in candidates:
                                           LET muting == {c \in cowns[self]: c \notin overloaded'} IN
                                             /\ unavailable' = (unavailable \union muting) \ unmute
                                             /\ mute_map' = ((receiver :> mute_map[receiver] \union muting) @@ mute_map)
                                             /\ available' = (available \union (cowns[self] \ muting) \union unmute)
                                 ELSE /\ unavailable' = unavailable \ unmute
                                      /\ available' = (available \union cowns[self] \union unmute)
                                      /\ mute_map' = [m \in unmute |-> {} ] @@ mute_map
                /\ refcount' = [c \in cowns[self] |-> refcount[c] - 1] @@ refcount
                /\ pc' = [pc EXCEPT ![self] = "Done"]
                /\ UNCHANGED << pending, running, untracked_behaviours, cowns >>

behaviour(self) == Create(self) \/ RCBarrier(self) \/ Acquire(self)
                      \/ Action(self)

(* Allow infinite stuttering to prevent deadlock on termination. *)
Terminating == /\ \A self \in ProcSet: pc[self] = "Done"
               /\ UNCHANGED vars

Next == (\E self \in Behaviours: behaviour(self))
           \/ Terminating

Spec == /\ Init /\ [][Next]_vars
        /\ \A self \in Behaviours : WF_vars(behaviour(self))

Termination == <>(\A self \in ProcSet: pc[self] = "Done")

\* END TRANSLATION - the hash of the generated TLA code (remove to silence divergence warnings): TLA-ae4715248db94d11539d4d27dbcfeb71

cownsUnavailable == \A b \in Behaviours: ~Intersects(cowns[b], available)

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
