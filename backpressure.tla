---- MODULE backpressure ----

(*
Assumptions:
  - Fairness (weakly fair behaviour process)
  - Cowns cannot become overloaded while muted.
  - Mute map entries will eventually be removed and unmuted.
    - Modeled by having overloaded cowns eventually become not overloaded.
*)

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
  \* Cowns that are overloaded
  overloaded = {},
  \* Cowns that are muted
  muted = {},
  \* Cowns that are protected
  protected = {},
  \* Mapping of mutor to muted
  mute_map = [c \in Cowns |-> {}],
  \* Count of behaviours that have yet to run on each cown
  refcount = [c \in Cowns |-> 0],
  \* Count of behaviours with untracked refcounts
  untracked_behaviours = Cardinality(Behaviours),

define
  \* Muted cowns must not be available, overloaded, or protected.
  MutedInv == ~Intersects(muted, UNION {available, overloaded, protected})
  \* All muted cowns must exist in at least one mute map entry.
  MuteMapInv == \A m \in muted: m \in UNION Range(mute_map)
  \* Refcounts must not drop below 0.
  RefcountInv == \A c \in Cowns: refcount[c] >= 0
  \* All refcounts must eventually drop to 0.
  RefcountDropInv ==
    (\A b \in Behaviours: pc[b] = "Done") => (\A c \in Cowns: refcount[c] = 0)

  \* All invalid mute map entries will eventually be removed.
  WillUnmute ==
    []<>(\A k \in DOMAIN mute_map: mute_map[k] = {} \/ k \in overloaded)

  \* Sending to receiver should mute senders.
  TriggersMuting(receiver) == receiver \in (overloaded \union muted)
  \* Cown cannot be muted.
  HasPriority(cown) == cown \in (overloaded \union protected)
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
      \* Protected receivers protect all other receivers
      if \E c \in required: HasPriority(c) then
        \* All previously muted cowns are unmuted when they become protected.
        \* TODO: drop protected state when RC from "priority" cowns is 0
        protected := protected \union remaining;
        available := available \union (remaining \intersect  muted);
        muted := muted \ remaining;
      end if;
    end with;
RunStep:
    with next = Min(required \ acquired) do
      \* Wait for the next required cown to become available.
      await (next \in available)
        \* TODO: this should be fixed, or implemented
        \/ ((next \in muted) /\ (\E c \in required: HasPriority(c)));
      if next \in available then
        \* Acquire the next cown and remove it from the available set.
        acquired := acquired \union {next};
        available := available \ {next};
      end if;
    end with;
  end while;

Action:
  assert \A c \in acquired: refcount[c] > 0;
  assert ~Intersects(acquired, muted);

  \* Any acquired cown may toggle their overloaded state when the behaviour
  \* completes.
  with overload \in SUBSET acquired do
    \* new value of overloaded is used to prevent muting later
    overloaded := (overloaded \ acquired) \union overload;
  end with;

  \* Select zero or one receiver with a nonzero refcount.
  with receiver \in Subsets({c \in Cowns: refcount[c] > 0}, 0, 1) do
    \* Mute senders if the receiver triggers muting and the receiver isn't one
    \* of the senders.
    if (receiver /= {})
      /\ ~Intersects(receiver, acquired)
      /\ TriggersMuting(Unwrap(receiver))
    then
      \* Mute senders that have no priority and are not becoming overloaded.
      with muting = {c \in acquired: ~HasPriority(c)} \ overloaded do
        muted := muted \union muting;
        \* Add muted senders to the mute map entry for the receiver.
        mute_map := [m \in receiver |-> mute_map[m] \union muting] @@ mute_map;
        available := available \union (acquired \ muting);
      end with;
    else
      \* Senders are not muted, so all become available.
      available := available \union acquired;
    end if;
  end with;

  \* Decrement the refcounts of all acquired cowns.
  refcount := [c \in acquired |-> refcount[c] - 1] @@ refcount;
  acquired := {};
end process;

fair+ process scheduler = 0
begin
RCBarrier:
  \* Wait for refcounts to be valid.
  await untracked_behaviours = 0;
MuteMapScan:
  \* Remove invalid mute map entries whenever they may exist.
  while (\E c \in Cowns: refcount[c] > 0) \/ (UNION Range(mute_map) /= {}) do
    with
      \* Invalid keys have a zero refcount or no longer trigger muting.
      keys = {c \in Cowns: (refcount[c] = 0) \/ ~TriggersMuting(c)},
      \* Unmute the range of all invalid keys.
      unmuting = UNION Range([k \in keys |-> mute_map[k]]),
    do
      \* Delete entries and unmute.
      mute_map := [k \in keys |-> {}] @@ mute_map;
      muted := muted \ unmuting;
      available := available \union unmuting;
    end with;
  end while;
end process;

end algorithm; *)

\* BEGIN TRANSLATION - the hash of the PCal code: PCal-1a664984619a118ef99c0017cbfb8d55
\* Label RCBarrier of process behaviour at line 77 col 3 changed to RCBarrier_
VARIABLES available, overloaded, muted, protected, mute_map, refcount, 
          untracked_behaviours, pc

(* define statement *)
MutedInv == ~Intersects(muted, UNION {available, overloaded, protected})

MuteMapInv == \A m \in muted: m \in UNION Range(mute_map)

RefcountInv == \A c \in Cowns: refcount[c] >= 0

RefcountDropInv ==
  (\A b \in Behaviours: pc[b] = "Done") => (\A c \in Cowns: refcount[c] = 0)


WillUnmute ==
  []<>(\A k \in DOMAIN mute_map: mute_map[k] = {} \/ k \in overloaded)


TriggersMuting(receiver) == receiver \in (overloaded \union muted)

HasPriority(cown) == cown \in (overloaded \union protected)

VARIABLES required, acquired

vars == << available, overloaded, muted, protected, mute_map, refcount, 
           untracked_behaviours, pc, required, acquired >>

ProcSet == (Behaviours) \cup {0}

Init == (* Global variables *)
        /\ available = Cowns
        /\ overloaded = {}
        /\ muted = {}
        /\ protected = {}
        /\ mute_map = [c \in Cowns |-> {}]
        /\ refcount = [c \in Cowns |-> 0]
        /\ untracked_behaviours = Cardinality(Behaviours)
        (* Process behaviour *)
        /\ required \in [Behaviours -> Subsets(Cowns, 0, 3)]
        /\ acquired = [self \in Behaviours |-> {}]
        /\ pc = [self \in ProcSet |-> CASE self \in Behaviours -> "Create"
                                        [] self = 0 -> "RCBarrier"]

Create(self) == /\ pc[self] = "Create"
                /\ refcount' = [c \in required[self] |-> refcount[c] + 1] @@ refcount
                /\ untracked_behaviours' = untracked_behaviours - 1
                /\ IF required[self] = {}
                      THEN /\ pc' = [pc EXCEPT ![self] = "Done"]
                      ELSE /\ pc' = [pc EXCEPT ![self] = "RCBarrier_"]
                /\ UNCHANGED << available, overloaded, muted, protected, 
                                mute_map, required, acquired >>

RCBarrier_(self) == /\ pc[self] = "RCBarrier_"
                    /\ untracked_behaviours = 0
                    /\ pc' = [pc EXCEPT ![self] = "Acquire"]
                    /\ UNCHANGED << available, overloaded, muted, protected, 
                                    mute_map, refcount, untracked_behaviours, 
                                    required, acquired >>

Acquire(self) == /\ pc[self] = "Acquire"
                 /\ IF required[self] /= acquired[self]
                       THEN /\ pc' = [pc EXCEPT ![self] = "Protect"]
                       ELSE /\ pc' = [pc EXCEPT ![self] = "Action"]
                 /\ UNCHANGED << available, overloaded, muted, protected, 
                                 mute_map, refcount, untracked_behaviours, 
                                 required, acquired >>

Protect(self) == /\ pc[self] = "Protect"
                 /\ LET remaining == required[self] \ acquired[self] IN
                      IF \E c \in required[self]: HasPriority(c)
                         THEN /\ protected' = (protected \union remaining)
                              /\ available' = (available \union (remaining \intersect  muted))
                              /\ muted' = muted \ remaining
                         ELSE /\ TRUE
                              /\ UNCHANGED << available, muted, protected >>
                 /\ pc' = [pc EXCEPT ![self] = "RunStep"]
                 /\ UNCHANGED << overloaded, mute_map, refcount, 
                                 untracked_behaviours, required, acquired >>

RunStep(self) == /\ pc[self] = "RunStep"
                 /\ LET next == Min(required[self] \ acquired[self]) IN
                      /\     (next \in available)
                         
                         \/ ((next \in muted) /\ (\E c \in required[self]: HasPriority(c)))
                      /\ IF next \in available
                            THEN /\ acquired' = [acquired EXCEPT ![self] = acquired[self] \union {next}]
                                 /\ available' = available \ {next}
                            ELSE /\ TRUE
                                 /\ UNCHANGED << available, acquired >>
                 /\ pc' = [pc EXCEPT ![self] = "Acquire"]
                 /\ UNCHANGED << overloaded, muted, protected, mute_map, 
                                 refcount, untracked_behaviours, required >>

Action(self) == /\ pc[self] = "Action"
                /\ Assert(\A c \in acquired[self]: refcount[c] > 0, 
                          "Failure of assertion at line 108, column 3.")
                /\ Assert(~Intersects(acquired[self], muted), 
                          "Failure of assertion at line 109, column 3.")
                /\ \E overload \in SUBSET acquired[self]:
                     overloaded' = ((overloaded \ acquired[self]) \union overload)
                /\ \E receiver \in Subsets({c \in Cowns: refcount[c] > 0}, 0, 1):
                     IF  (receiver /= {})
                        /\ ~Intersects(receiver, acquired[self])
                        /\ TriggersMuting(Unwrap(receiver))
                        THEN /\ LET muting == {c \in acquired[self]: ~HasPriority(c)} \ overloaded' IN
                                  /\ muted' = (muted \union muting)
                                  /\ mute_map' = [m \in receiver |-> mute_map[m] \union muting] @@ mute_map
                                  /\ available' = (available \union (acquired[self] \ muting))
                        ELSE /\ available' = (available \union acquired[self])
                             /\ UNCHANGED << muted, mute_map >>
                /\ refcount' = [c \in acquired[self] |-> refcount[c] - 1] @@ refcount
                /\ acquired' = [acquired EXCEPT ![self] = {}]
                /\ pc' = [pc EXCEPT ![self] = "Done"]
                /\ UNCHANGED << protected, untracked_behaviours, required >>

behaviour(self) == Create(self) \/ RCBarrier_(self) \/ Acquire(self)
                      \/ Protect(self) \/ RunStep(self) \/ Action(self)

RCBarrier == /\ pc[0] = "RCBarrier"
             /\ untracked_behaviours = 0
             /\ pc' = [pc EXCEPT ![0] = "MuteMapScan"]
             /\ UNCHANGED << available, overloaded, muted, protected, mute_map, 
                             refcount, untracked_behaviours, required, 
                             acquired >>

MuteMapScan == /\ pc[0] = "MuteMapScan"
               /\ IF (\E c \in Cowns: refcount[c] > 0) \/ (UNION Range(mute_map) /= {})
                     THEN /\ LET keys == {c \in Cowns: (refcount[c] = 0) \/ ~TriggersMuting(c)} IN
                               LET unmuting == UNION Range([k \in keys |-> mute_map[k]]) IN
                                 /\ mute_map' = [k \in keys |-> {}] @@ mute_map
                                 /\ muted' = muted \ unmuting
                                 /\ available' = (available \union unmuting)
                          /\ pc' = [pc EXCEPT ![0] = "MuteMapScan"]
                     ELSE /\ pc' = [pc EXCEPT ![0] = "Done"]
                          /\ UNCHANGED << available, muted, mute_map >>
               /\ UNCHANGED << overloaded, protected, refcount, 
                               untracked_behaviours, required, acquired >>

scheduler == RCBarrier \/ MuteMapScan

(* Allow infinite stuttering to prevent deadlock on termination. *)
Terminating == /\ \A self \in ProcSet: pc[self] = "Done"
               /\ UNCHANGED vars

Next == scheduler
           \/ (\E self \in Behaviours: behaviour(self))
           \/ Terminating

Spec == /\ Init /\ [][Next]_vars
        /\ \A self \in Behaviours : WF_vars(behaviour(self))
        /\ SF_vars(scheduler)

Termination == <>(\A self \in ProcSet: pc[self] = "Done")

\* END TRANSLATION - the hash of the generated TLA code (remove to silence divergence warnings): TLA-f5051a41e23942d731a94f2cf058252c

AcquiredUnavailable == \A b \in Behaviours: ~Intersects(acquired[b], available)

====
