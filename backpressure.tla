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
  available = Cowns,
  overloaded = {},
  muted = {},
  unblocked = {},
  mute_map = [c \in Cowns |-> {}],
  refcount = [c \in Cowns |-> 0],
  untracked_behaviours = Cardinality(Behaviours);

define
  MutedInv == ~Intersects(muted, UNION {unblocked, overloaded, available})
  UnmutableInv == ~Intersects(unblocked, muted)
  MuteMapInv == \A m \in muted: m \in UNION Range(mute_map)
  RefcountInv == \A c \in Cowns: refcount[c] >= 0
  RefcountDropInv ==
    (\A b \in Behaviours: pc[b] = "Done") => (\A c \in Cowns: refcount[c] = 0)

  WillUnmute ==
    []<>(\A k \in DOMAIN mute_map: mute_map[k] = {} \/ k \in overloaded)

  TriggersMute(mutor) ==
    (refcount[mutor] > 0) /\ (mutor \in (overloaded \union muted))
  RequiresUnblock(cown) ==
    (refcount[cown] > 0) /\ (cown \in (overloaded \union unblocked))
end define;

fair process behaviour \in Behaviours
variables
  required \in Subsets(Cowns, 0, 3),
  acquired = {},
begin
Create:
  refcount := [c \in required |-> refcount[c] + 1] @@ refcount;
  untracked_behaviours := untracked_behaviours - 1;
  \* Empty required set used to represent fewer behaviours in the system.
  if required = {} then goto Done; end if;

RCBarrier:
  await untracked_behaviours = 0;

Acquire:
  while required /= acquired do
Unblock:
    with remaining = required \ acquired do
      if Intersects(required, overloaded \union unblocked) then
        \* TODO: drop unblocked state when RC from "priority" cowns is 0
        unblocked := unblocked \union remaining;
        available := available \union (remaining \intersect  muted);
        muted := muted \ remaining;
      end if;
    end with;
AcquireInner:
    with next = Min(required \ acquired) do
      await (next \in available)
        \* TODO: this should be fixed, or implemented
        \/ (Intersects(required, overloaded \union unblocked)
            /\ (next \in muted));
      if next \in available then
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

  with receiver \in Subsets(Cowns, 0, 1) do
    if (receiver /= {})
      /\ ~Intersects(receiver, acquired)
      /\ TriggersMute(Unwrap(receiver))
    then
      \* don't mute the cowns getting overloaded
      with muting = {c \in acquired: ~RequiresUnblock(c)} \ overloaded do
        muted := muted \union muting;
        mute_map := [m \in receiver |-> mute_map[m] \union muting] @@ mute_map;
        available := available \union (acquired \ muting);
      end with;
    else
      available := available \union acquired;
    end if;
  end with;

  refcount := [c \in acquired |-> refcount[c] - 1] @@ refcount;
  acquired := {};
end process;

fair+ process scheduler = 0
begin
RCBarrier:
  await untracked_behaviours = 0;
Scan:
  while (\E c \in Cowns: refcount[c] > 0) \/ (UNION Range(mute_map) /= {}) do
    with
      keys = {c \in Cowns: ~TriggersMute(c)},
      unmuting = UNION Range([k \in keys |-> mute_map[k]]),
    do
      mute_map := [k \in keys |-> {}] @@ mute_map;
      muted := muted \ unmuting;
      available := available \union unmuting;
    end with;
  end while;
end process;

end algorithm; *)

\* BEGIN TRANSLATION - the hash of the PCal code: PCal-37f088d70cd47a2804bd5546898a8a09
\* Label RCBarrier of process behaviour at line 63 col 3 changed to RCBarrier_
VARIABLES available, overloaded, muted, unblocked, mute_map, refcount, 
          untracked_behaviours, pc

(* define statement *)
MutedInv == ~Intersects(muted, UNION {unblocked, overloaded, available})
UnmutableInv == ~Intersects(unblocked, muted)
MuteMapInv == \A m \in muted: m \in UNION Range(mute_map)
RefcountInv == \A c \in Cowns: refcount[c] >= 0
RefcountDropInv ==
  (\A b \in Behaviours: pc[b] = "Done") => (\A c \in Cowns: refcount[c] = 0)

WillUnmute ==
  []<>(\A k \in DOMAIN mute_map: mute_map[k] = {} \/ k \in overloaded)

TriggersMute(mutor) ==
  (refcount[mutor] > 0) /\ (mutor \in (overloaded \union muted))
RequiresUnblock(cown) ==
  (refcount[cown] > 0) /\ (cown \in (overloaded \union unblocked))

VARIABLES required, acquired

vars == << available, overloaded, muted, unblocked, mute_map, refcount, 
           untracked_behaviours, pc, required, acquired >>

ProcSet == (Behaviours) \cup {0}

Init == (* Global variables *)
        /\ available = Cowns
        /\ overloaded = {}
        /\ muted = {}
        /\ unblocked = {}
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
                /\ UNCHANGED << available, overloaded, muted, unblocked, 
                                mute_map, required, acquired >>

RCBarrier_(self) == /\ pc[self] = "RCBarrier_"
                    /\ untracked_behaviours = 0
                    /\ pc' = [pc EXCEPT ![self] = "Acquire"]
                    /\ UNCHANGED << available, overloaded, muted, unblocked, 
                                    mute_map, refcount, untracked_behaviours, 
                                    required, acquired >>

Acquire(self) == /\ pc[self] = "Acquire"
                 /\ IF required[self] /= acquired[self]
                       THEN /\ pc' = [pc EXCEPT ![self] = "Unblock"]
                       ELSE /\ pc' = [pc EXCEPT ![self] = "Action"]
                 /\ UNCHANGED << available, overloaded, muted, unblocked, 
                                 mute_map, refcount, untracked_behaviours, 
                                 required, acquired >>

Unblock(self) == /\ pc[self] = "Unblock"
                 /\ LET remaining == required[self] \ acquired[self] IN
                      IF Intersects(required[self], overloaded \union unblocked)
                         THEN /\ unblocked' = (unblocked \union remaining)
                              /\ available' = (available \union (remaining \intersect  muted))
                              /\ muted' = muted \ remaining
                         ELSE /\ TRUE
                              /\ UNCHANGED << available, muted, unblocked >>
                 /\ pc' = [pc EXCEPT ![self] = "AcquireInner"]
                 /\ UNCHANGED << overloaded, mute_map, refcount, 
                                 untracked_behaviours, required, acquired >>

AcquireInner(self) == /\ pc[self] = "AcquireInner"
                      /\ LET next == Min(required[self] \ acquired[self]) IN
                           /\     (next \in available)
                              
                              \/ (Intersects(required[self], overloaded \union unblocked)
                                  /\ (next \in muted))
                           /\ IF next \in available
                                 THEN /\ acquired' = [acquired EXCEPT ![self] = acquired[self] \union {next}]
                                      /\ available' = available \ {next}
                                 ELSE /\ TRUE
                                      /\ UNCHANGED << available, acquired >>
                      /\ pc' = [pc EXCEPT ![self] = "Acquire"]
                      /\ UNCHANGED << overloaded, muted, unblocked, mute_map, 
                                      refcount, untracked_behaviours, required >>

Action(self) == /\ pc[self] = "Action"
                /\ Assert(\A c \in acquired[self]: refcount[c] > 0, 
                          "Failure of assertion at line 90, column 3.")
                /\ Assert(~Intersects(acquired[self], muted), 
                          "Failure of assertion at line 91, column 3.")
                /\ \E overload \in SUBSET acquired[self]:
                     overloaded' = ((overloaded \ acquired[self]) \union overload)
                /\ \E receiver \in Subsets(Cowns, 0, 1):
                     IF  (receiver /= {})
                        /\ ~Intersects(receiver, acquired[self])
                        /\ TriggersMute(Unwrap(receiver))
                        THEN /\ LET muting == {c \in acquired[self]: ~RequiresUnblock(c)} \ overloaded' IN
                                  /\ muted' = (muted \union muting)
                                  /\ mute_map' = [m \in receiver |-> mute_map[m] \union muting] @@ mute_map
                                  /\ available' = (available \union (acquired[self] \ muting))
                        ELSE /\ available' = (available \union acquired[self])
                             /\ UNCHANGED << muted, mute_map >>
                /\ refcount' = [c \in acquired[self] |-> refcount[c] - 1] @@ refcount
                /\ acquired' = [acquired EXCEPT ![self] = {}]
                /\ pc' = [pc EXCEPT ![self] = "Done"]
                /\ UNCHANGED << unblocked, untracked_behaviours, required >>

behaviour(self) == Create(self) \/ RCBarrier_(self) \/ Acquire(self)
                      \/ Unblock(self) \/ AcquireInner(self)
                      \/ Action(self)

RCBarrier == /\ pc[0] = "RCBarrier"
             /\ untracked_behaviours = 0
             /\ pc' = [pc EXCEPT ![0] = "Scan"]
             /\ UNCHANGED << available, overloaded, muted, unblocked, mute_map, 
                             refcount, untracked_behaviours, required, 
                             acquired >>

Scan == /\ pc[0] = "Scan"
        /\ IF (\E c \in Cowns: refcount[c] > 0) \/ (UNION Range(mute_map) /= {})
              THEN /\ LET keys == {c \in Cowns: ~TriggersMute(c)} IN
                        LET unmuting == UNION Range([k \in keys |-> mute_map[k]]) IN
                          /\ mute_map' = [k \in keys |-> {}] @@ mute_map
                          /\ muted' = muted \ unmuting
                          /\ available' = (available \union unmuting)
                   /\ pc' = [pc EXCEPT ![0] = "Scan"]
              ELSE /\ pc' = [pc EXCEPT ![0] = "Done"]
                   /\ UNCHANGED << available, muted, mute_map >>
        /\ UNCHANGED << overloaded, unblocked, refcount, untracked_behaviours, 
                        required, acquired >>

scheduler == RCBarrier \/ Scan

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

\* END TRANSLATION - the hash of the generated TLA code (remove to silence divergence warnings): TLA-61f860efb679affb2f5301956bf40106

AcquiredUnavailable == \A b \in Behaviours: ~Intersects(acquired[b], available)

====
