---- MODULE backpressure ----

\* pcal backpressure.tla && TLA_JAVA=/usr/lib/jvm/java-14-openjdk/bin/java tlc backpressure.tla -workers 8

\* Note: Each while iteration is an atomic step.

EXTENDS TLC, Integers, FiniteSets

Cowns == 1..3 \* TODO: more

Subsets(s, min, max) ==
  {cs \in SUBSET s : Cardinality(cs) >= min /\ Cardinality(cs) <= max}

DisjunctiveUnion(a, b) == (a \union b) \ (a \cap b)
Range(f) == {f[x] : x \in DOMAIN f}
Min(s) == CHOOSE x \in s: \A y \in s \ {x}: y > x

(* --algorithm backpressure

variables
  available = Cowns,
  overloaded = {},
  muted = {},
  unmutable = {},
  mute_map = [c \in Cowns |-> {}],
  refcount = [c \in Cowns |-> 0],
  rc_barrier = 0;

define
  BehaviourCount == 3 \* TODO: more
end define;

fair process behaviour \in 1..BehaviourCount
variables
  required \in Subsets(Cowns, 1, 3), next, acquired = {}, mutor, muting = {}
begin
Send:
  refcount :=
    [c \in Cowns |-> IF c \in required THEN refcount[c] + 1 ELSE refcount[c]];
  rc_barrier := rc_barrier + 1;
Unmute:
  while DisjunctiveUnion(required, unmutable) /= {} do
    next := Min(DisjunctiveUnion(required, unmutable));
    if next \in muted then
      muted := muted \ {next};
      available := available \union {next};
    end if;
    unmutable := unmutable \union {next};
  end while;
Acquire:
  while required /= {} do
    next := Min(required);
    await next \in available;
    acquired := acquired \union {next};
    required := required \ {next};
    available := available \ {next};
  end while;
Action:
  assert required = {};
  with overloading \in Subsets(acquired \ muted, 0, 3) do
    overloaded := overloaded \union overloading;
  end with;
  if (overloaded /= {}) /\ (acquired \cap overloaded = {}) then
    either
      with mutor_ \in overloaded do mutor := mutor_ end with;
      muting := (acquired \ unmutable);
    or
      skip;
    end either;
  end if;
Complete:
  if mutor /= defaultInitValue then
    muted := muted \union muting;
    mute_map[mutor] := mute_map[mutor] \union muting;
  end if;
  available := available \union (acquired \ muting);
  muting := {};
  refcount :=
    [c \in Cowns |-> IF c \in acquired THEN refcount[c] - 1 ELSE refcount[c]];
  acquired := {};
  assert acquired \union required = {};
end process;

fair process mute_map_scan = 0
  variables next;
begin
BarrierWait:
  await rc_barrier = BehaviourCount;
MutorWait:
  while \E c \in Cowns : mute_map[c] /= {} do
    await \E c \in Cowns : (mute_map[c] /= {}) /\ (refcount[c] = 0);
UnmuteSet:
    next := CHOOSE c \in Cowns : (mute_map[c] /= {}) /\ (refcount[c] = 0);
    muted := muted \ mute_map[next];
    available := available \union mute_map[next];
    mute_map[next] := {};
  end while;
end process;

end algorithm; *)

\* BEGIN TRANSLATION - the hash of the PCal code: PCal-f3283cc8515383a88a2aadd5b9310ea5
\* Process variable next of process behaviour at line 35 col 38 changed to next_
CONSTANT defaultInitValue
VARIABLES available, overloaded, muted, unmutable, mute_map, refcount,
          rc_barrier, pc

(* define statement *)
BehaviourCount == 3

VARIABLES required, next_, acquired, mutor, muting, next

vars == << available, overloaded, muted, unmutable, mute_map, refcount,
           rc_barrier, pc, required, next_, acquired, mutor, muting, next >>

ProcSet == (1..BehaviourCount) \cup {0}

Init == (* Global variables *)
        /\ available = Cowns
        /\ overloaded = {}
        /\ muted = {}
        /\ unmutable = {}
        /\ mute_map = [c \in Cowns |-> {}]
        /\ refcount = [c \in Cowns |-> 0]
        /\ rc_barrier = 0
        (* Process behaviour *)
        /\ required \in [1..BehaviourCount -> Subsets(Cowns, 1, 3)]
        /\ next_ = [self \in 1..BehaviourCount |-> defaultInitValue]
        /\ acquired = [self \in 1..BehaviourCount |-> {}]
        /\ mutor = [self \in 1..BehaviourCount |-> defaultInitValue]
        /\ muting = [self \in 1..BehaviourCount |-> {}]
        (* Process mute_map_scan *)
        /\ next = defaultInitValue
        /\ pc = [self \in ProcSet |-> CASE self \in 1..BehaviourCount -> "Send"
                                        [] self = 0 -> "BarrierWait"]

Send(self) == /\ pc[self] = "Send"
              /\ refcount' = [c \in Cowns |-> IF c \in required[self] THEN refcount[c] + 1 ELSE refcount[c]]
              /\ rc_barrier' = rc_barrier + 1
              /\ pc' = [pc EXCEPT ![self] = "Unmute"]
              /\ UNCHANGED << available, overloaded, muted, unmutable,
                              mute_map, required, next_, acquired, mutor,
                              muting, next >>

Unmute(self) == /\ pc[self] = "Unmute"
                /\ IF DisjunctiveUnion(required[self], unmutable) /= {}
                      THEN /\ next_' = [next_ EXCEPT ![self] = Min(DisjunctiveUnion(required[self], unmutable))]
                           /\ IF next_'[self] \in muted
                                 THEN /\ muted' = muted \ {next_'[self]}
                                      /\ available' = (available \union {next_'[self]})
                                 ELSE /\ TRUE
                                      /\ UNCHANGED << available, muted >>
                           /\ unmutable' = (unmutable \union {next_'[self]})
                           /\ pc' = [pc EXCEPT ![self] = "Unmute"]
                      ELSE /\ pc' = [pc EXCEPT ![self] = "Acquire"]
                           /\ UNCHANGED << available, muted, unmutable, next_ >>
                /\ UNCHANGED << overloaded, mute_map, refcount, rc_barrier,
                                required, acquired, mutor, muting, next >>

Acquire(self) == /\ pc[self] = "Acquire"
                 /\ IF required[self] /= {}
                       THEN /\ next_' = [next_ EXCEPT ![self] = Min(required[self])]
                            /\ next_'[self] \in available
                            /\ acquired' = [acquired EXCEPT ![self] = acquired[self] \union {next_'[self]}]
                            /\ required' = [required EXCEPT ![self] = required[self] \ {next_'[self]}]
                            /\ available' = available \ {next_'[self]}
                            /\ pc' = [pc EXCEPT ![self] = "Acquire"]
                       ELSE /\ pc' = [pc EXCEPT ![self] = "Action"]
                            /\ UNCHANGED << available, required, next_,
                                            acquired >>
                 /\ UNCHANGED << overloaded, muted, unmutable, mute_map,
                                 refcount, rc_barrier, mutor, muting, next >>

Action(self) == /\ pc[self] = "Action"
                /\ Assert(required[self] = {},
                          "Failure of assertion at line 59, column 3.")
                /\ \E overloading \in Subsets(acquired[self] \ muted, 0, 3):
                     overloaded' = (overloaded \union overloading)
                /\ IF (overloaded' /= {}) /\ (acquired[self] \cap overloaded' = {})
                      THEN /\ \/ /\ \E mutor_ \in overloaded':
                                      mutor' = [mutor EXCEPT ![self] = mutor_]
                                 /\ muting' = [muting EXCEPT ![self] = (acquired[self] \ unmutable)]
                              \/ /\ TRUE
                                 /\ UNCHANGED <<mutor, muting>>
                      ELSE /\ TRUE
                           /\ UNCHANGED << mutor, muting >>
                /\ pc' = [pc EXCEPT ![self] = "Complete"]
                /\ UNCHANGED << available, muted, unmutable, mute_map,
                                refcount, rc_barrier, required, next_,
                                acquired, next >>

Complete(self) == /\ pc[self] = "Complete"
                  /\ IF mutor[self] /= defaultInitValue
                        THEN /\ muted' = (muted \union muting[self])
                             /\ mute_map' = [mute_map EXCEPT ![mutor[self]] = mute_map[mutor[self]] \union muting[self]]
                        ELSE /\ TRUE
                             /\ UNCHANGED << muted, mute_map >>
                  /\ available' = (available \union (acquired[self] \ muting[self]))
                  /\ muting' = [muting EXCEPT ![self] = {}]
                  /\ refcount' = [c \in Cowns |-> IF c \in acquired[self] THEN refcount[c] - 1 ELSE refcount[c]]
                  /\ acquired' = [acquired EXCEPT ![self] = {}]
                  /\ Assert(acquired'[self] \union required[self] = {},
                            "Failure of assertion at line 81, column 3.")
                  /\ pc' = [pc EXCEPT ![self] = "Done"]
                  /\ UNCHANGED << overloaded, unmutable, rc_barrier, required,
                                  next_, mutor, next >>

behaviour(self) == Send(self) \/ Unmute(self) \/ Acquire(self)
                      \/ Action(self) \/ Complete(self)

BarrierWait == /\ pc[0] = "BarrierWait"
               /\ rc_barrier = BehaviourCount
               /\ pc' = [pc EXCEPT ![0] = "MutorWait"]
               /\ UNCHANGED << available, overloaded, muted, unmutable,
                               mute_map, refcount, rc_barrier, required, next_,
                               acquired, mutor, muting, next >>

MutorWait == /\ pc[0] = "MutorWait"
             /\ IF \E c \in Cowns : mute_map[c] /= {}
                   THEN /\ \E c \in Cowns : (mute_map[c] /= {}) /\ (refcount[c] = 0)
                        /\ pc' = [pc EXCEPT ![0] = "UnmuteSet"]
                   ELSE /\ pc' = [pc EXCEPT ![0] = "Done"]
             /\ UNCHANGED << available, overloaded, muted, unmutable, mute_map,
                             refcount, rc_barrier, required, next_, acquired,
                             mutor, muting, next >>

UnmuteSet == /\ pc[0] = "UnmuteSet"
             /\ next' = (CHOOSE c \in Cowns : (mute_map[c] /= {}) /\ (refcount[c] = 0))
             /\ muted' = muted \ mute_map[next']
             /\ available' = (available \union mute_map[next'])
             /\ mute_map' = [mute_map EXCEPT ![next'] = {}]
             /\ pc' = [pc EXCEPT ![0] = "MutorWait"]
             /\ UNCHANGED << overloaded, unmutable, refcount, rc_barrier,
                             required, next_, acquired, mutor, muting >>

mute_map_scan == BarrierWait \/ MutorWait \/ UnmuteSet

(* Allow infinite stuttering to prevent deadlock on termination. *)
Terminating == /\ \A self \in ProcSet: pc[self] = "Done"
               /\ UNCHANGED vars

Next == mute_map_scan
           \/ (\E self \in 1..BehaviourCount: behaviour(self))
           \/ Terminating

Spec == /\ Init /\ [][Next]_vars
        /\ \A self \in 1..BehaviourCount : WF_vars(behaviour(self))
        /\ WF_vars(mute_map_scan)

Termination == <>(\A self \in ProcSet: pc[self] = "Done")

\* END TRANSLATION - the hash of the generated TLA code (remove to silence divergence warnings): TLA-1e821d772df9fdccd2826e827f1e2b1f

MutedInv == available \intersect muted = {}
UnmutableInv == (overloaded \union unmutable) \cap muted = {}
RefcountInv == \A c \in Cowns : refcount[c] >= 0
MuteMapInv == \A m \in muted : m \in UNION Range(mute_map)
MuteSetInv == \A k \in DOMAIN mute_map : (mute_map[k] = {}) \/ (k \in overloaded)

TypeCorrect == MutedInv /\ UnmutableInv /\ RefcountInv /\ MuteMapInv /\ MuteSetInv

RefcountDrop == <>[](\A c \in Cowns : refcount[c] = 0)

\* Correct == Termination

====
