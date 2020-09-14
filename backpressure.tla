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

(* --algorithm backpressure

variables
  \* Cowns available for running behaviours
  available = Cowns,
  \* Cowns that are unavailable
  unavailable = {},
  \* Cowns that are overloaded
  overloaded = {},
  \* Cowns that are protected
  protected = {},
  \* Mapping of mutor to unavailable
  mute_map = [c \in Cowns |-> {}],
  \* Count of behaviours that have yet to run on each cown
  refcount = [c \in Cowns |-> 0],
  \* Count of behaviours with untracked refcounts
  untracked_behaviours = Cardinality(Behaviours),

define
  \* unavailable cowns must not be available, overloaded, or protected.
  UnavailableInv == ~Intersects(unavailable, UNION {available, overloaded, protected})
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
  HasPriority(cown) == cown \in (overloaded \union protected)
  
  \* Overloaded(cown) == refcount[c] > threshold
  \* Protected(cown) == \E b \in behaviours, c \in Cowns: cown \in behaviours[b] /\ c \in behaviours[b] /\ Overloaded(c)
end define;

fair process behaviour \in Behaviours
variables
  required \in Subsets(Cowns, 0, 3),
  acquired = {},
begin
Create:
  \* Add a refcount to all required cowns.
  refcount := [c \in required |-> refcount[c] + 1] @@ refcount;
  \* Indicate that the refcounts for this behaviour have been tracked.
  untracked_behaviours := untracked_behaviours - 1;
  \* Empty required set used to represent fewer behaviours in the system.
  if required = {} then goto Done; end if;

RCBarrier:
  \* Wait for refcounts to be valid.
  await untracked_behaviours = 0;

Acquire:
  \* Acquire all cowns, one at a time.
  while required /= acquired do
Protect:
    with remaining = required \ acquired do
      \* Priority (overloaded or protected) receivers protect all other
      \* receivers.
      if \E c \in required: HasPriority(c) then
        \* All previously unavailable cowns are ununavailable when they become protected.
        \* TODO: drop protected state when RC from "priority" cowns is 0
        protected := protected \union remaining;
        available := available \union (remaining \intersect  unavailable);
        unavailable := unavailable \ remaining;
      end if;
    end with;
AcquireNext:
    with next = Min(required \ acquired) do
      \* Wait for the next required cown to become available.
      await (next \in available);
        \* TODO: see note at bottom of file
        \* \/ ((next \in unavailable) /\ (\E c \in required: HasPriority(c)));
        \* why does this prevent termination?
      if next \in available then
        \* Acquire the next cown and remove it from the available set.
        acquired := acquired \union {next};
        available := available \ {next};
      end if;
    end with;
  end while;

Action:
  assert \A c \in acquired: refcount[c] > 0;
  assert ~Intersects(acquired, unavailable);

  \* Any acquired cown may toggle their overloaded state when the behaviour
  \* completes.
  with overload \in SUBSET Cowns,
       unoverload \in SUBSET (acquired \ overloaded),
       unmute = unavailable \ {c \in Cowns : (\E u \in (DOMAIN mute_map \ unoverload): c \in mute_map[u])} \* pick those we muted that are not in anybody elses mute set
  do 
    overloaded := (overloaded \ unoverload) \union overloaded;
  
    \* Mute senders if the receiver triggers muting and the receiver isn't one
    \* of the senders.
    with candidates = {c \in Cowns: refcount[c] > 0 /\ c \notin acquired /\ TriggersMuting(c)} do
      if candidates /= {} then
        with receiver \in candidates, muting = {c \in acquired: ~HasPriority(c)} \ overloaded do \* /\ refcount[receiver] > 0 do
          unavailable := (unavailable \union muting) \ unmute;
          \* Add unavailable senders to the mute map entry for the receiver.
          mute_map := ([m \in receiver |-> mute_map[m] \union muting] @@ mute_map) \ unmute;
          available := available \union (acquired \ muting) \union unmute;
        end with;
      else
        \* Senders are not unavailable, so all become available.
        unavailable := unavailable \ unmute;
        available := available \union acquired \union unmute;
        mute_map := [m \in unmute |-> {} ] @@ mute_map;
      end if;
    end with;
  end with;

  \* Decrement the refcounts of all acquired cowns.
  refcount := [c \in acquired |-> refcount[c] - 1] @@ refcount;
  acquired := {};
end process;

end algorithm; *)
\* BEGIN TRANSLATION - the hash of the PCal code: PCal-be07efcd40312b3da12a683a12a90f60
VARIABLES available, unavailable, overloaded, protected, mute_map, refcount, 
          untracked_behaviours, pc

(* define statement *)
UnavailableInv == ~Intersects(unavailable, UNION {available, overloaded, protected})

MuteMapInv == \A m \in unavailable: m \in UNION Range(mute_map)


ReverseInv == \A m \in UNION Range(mute_map): m \in unavailable


RefcountInv == \A c \in Cowns: refcount[c] >= 0

RefcountDropInv ==
  (\A b \in Behaviours: pc[b] = "Done") => (\A c \in Cowns: refcount[c] = 0)


MuteMapProp ==
  []<>(\A k \in DOMAIN mute_map: mute_map[k] = {} \/ k \in overloaded)


TriggersMuting(receiver) == receiver \in (overloaded \union unavailable)

HasPriority(cown) == cown \in (overloaded \union protected)

VARIABLES required, acquired

vars == << available, unavailable, overloaded, protected, mute_map, refcount, 
           untracked_behaviours, pc, required, acquired >>

ProcSet == (Behaviours)

Init == (* Global variables *)
        /\ available = Cowns
        /\ unavailable = {}
        /\ overloaded = {}
        /\ protected = {}
        /\ mute_map = [c \in Cowns |-> {}]
        /\ refcount = [c \in Cowns |-> 0]
        /\ untracked_behaviours = Cardinality(Behaviours)
        (* Process behaviour *)
        /\ required \in [Behaviours -> Subsets(Cowns, 0, 3)]
        /\ acquired = [self \in Behaviours |-> {}]
        /\ pc = [self \in ProcSet |-> "Create"]

Create(self) == /\ pc[self] = "Create"
                /\ refcount' = [c \in required[self] |-> refcount[c] + 1] @@ refcount
                /\ untracked_behaviours' = untracked_behaviours - 1
                /\ IF required[self] = {}
                      THEN /\ pc' = [pc EXCEPT ![self] = "Done"]
                      ELSE /\ pc' = [pc EXCEPT ![self] = "RCBarrier"]
                /\ UNCHANGED << available, unavailable, overloaded, protected, 
                                mute_map, required, acquired >>

RCBarrier(self) == /\ pc[self] = "RCBarrier"
                   /\ untracked_behaviours = 0
                   /\ pc' = [pc EXCEPT ![self] = "Acquire"]
                   /\ UNCHANGED << available, unavailable, overloaded, 
                                   protected, mute_map, refcount, 
                                   untracked_behaviours, required, acquired >>

Acquire(self) == /\ pc[self] = "Acquire"
                 /\ IF required[self] /= acquired[self]
                       THEN /\ pc' = [pc EXCEPT ![self] = "Protect"]
                       ELSE /\ pc' = [pc EXCEPT ![self] = "Action"]
                 /\ UNCHANGED << available, unavailable, overloaded, protected, 
                                 mute_map, refcount, untracked_behaviours, 
                                 required, acquired >>

Protect(self) == /\ pc[self] = "Protect"
                 /\ LET remaining == required[self] \ acquired[self] IN
                      IF \E c \in required[self]: HasPriority(c)
                         THEN /\ protected' = (protected \union remaining)
                              /\ available' = (available \union (remaining \intersect  unavailable))
                              /\ unavailable' = unavailable \ remaining
                         ELSE /\ TRUE
                              /\ UNCHANGED << available, unavailable, 
                                              protected >>
                 /\ pc' = [pc EXCEPT ![self] = "AcquireNext"]
                 /\ UNCHANGED << overloaded, mute_map, refcount, 
                                 untracked_behaviours, required, acquired >>

AcquireNext(self) == /\ pc[self] = "AcquireNext"
                     /\ LET next == Min(required[self] \ acquired[self]) IN
                          /\ (next \in available)
                          /\ IF next \in available
                                THEN /\ acquired' = [acquired EXCEPT ![self] = acquired[self] \union {next}]
                                     /\ available' = available \ {next}
                                ELSE /\ TRUE
                                     /\ UNCHANGED << available, acquired >>
                     /\ pc' = [pc EXCEPT ![self] = "Acquire"]
                     /\ UNCHANGED << unavailable, overloaded, protected, 
                                     mute_map, refcount, untracked_behaviours, 
                                     required >>

Action(self) == /\ pc[self] = "Action"
                /\ Assert(\A c \in acquired[self]: refcount[c] > 0, 
                          "Failure of assertion at line 109, column 3.")
                /\ Assert(~Intersects(acquired[self], unavailable), 
                          "Failure of assertion at line 110, column 3.")
                /\ \E overload \in SUBSET Cowns:
                     \E unoverload \in SUBSET (acquired[self] \ overloaded):
                       LET unmute == unavailable \ {c \in Cowns : (\E u \in (DOMAIN mute_map \ unoverload): c \in mute_map[u])} IN
                         /\ overloaded' = ((overloaded \ unoverload) \union overloaded)
                         /\ LET candidates == {c \in Cowns: refcount[c] > 0 /\ c \notin acquired[self] /\ TriggersMuting(c)} IN
                              IF candidates /= {}
                                 THEN /\ \E receiver \in candidates:
                                           LET muting == {c \in acquired[self]: ~HasPriority(c)} \ overloaded' IN
                                             /\ unavailable' = (unavailable \union muting) \ unmute
                                             /\ mute_map' = ([m \in receiver |-> mute_map[m] \union muting] @@ mute_map) \ unmute
                                             /\ available' = (available \union (acquired[self] \ muting) \union unmute)
                                 ELSE /\ unavailable' = unavailable \ unmute
                                      /\ available' = (available \union acquired[self] \union unmute)
                                      /\ mute_map' = [m \in unmute |-> {} ] @@ mute_map
                /\ refcount' = [c \in acquired[self] |-> refcount[c] - 1] @@ refcount
                /\ acquired' = [acquired EXCEPT ![self] = {}]
                /\ pc' = [pc EXCEPT ![self] = "Done"]
                /\ UNCHANGED << protected, untracked_behaviours, required >>

behaviour(self) == Create(self) \/ RCBarrier(self) \/ Acquire(self)
                      \/ Protect(self) \/ AcquireNext(self) \/ Action(self)

(* Allow infinite stuttering to prevent deadlock on termination. *)
Terminating == /\ \A self \in ProcSet: pc[self] = "Done"
               /\ UNCHANGED vars

Next == (\E self \in Behaviours: behaviour(self))
           \/ Terminating

Spec == /\ Init /\ [][Next]_vars
        /\ \A self \in Behaviours : WF_vars(behaviour(self))

Termination == <>(\A self \in ProcSet: pc[self] = "Done")

\* END TRANSLATION - the hash of the generated TLA code (remove to silence divergence warnings): TLA-c6d56c0a1e80cb53faa4ebdb1a06b17d

AcquiredUnavailable == \A b \in Behaviours: ~Intersects(acquired[b], available)

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
