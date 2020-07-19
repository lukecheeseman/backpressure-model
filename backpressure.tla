---- MODULE backpressure ----

(*
Assumptions:
  - Fairness (weakly fair behaviour process)
  - Cowns cannot become overloaded while muted.
  - Mute map entries will eventually be removed and unmuted.
    - Modeled by having overloaded cowns eventually become not overloaded.

Note:
  - Each while iteration is an atomic step.
*)

EXTENDS TLC, Integers, FiniteSets

Cowns == 1..4

Range(f) == {f[x] : x \in DOMAIN f}
Min(s) == CHOOSE x \in s: \A y \in s \ {x}: y > x
Subsets(s, min, max) ==
  {cs \in SUBSET s : Cardinality(cs) >= min /\ Cardinality(cs) <= max}

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
  BehaviourCount == 3

  MutedInv == available \intersect muted = {}
  \* TODO: []<>(unmutable \intersect muted = {})
  UnmutableInv == overloaded \intersect muted = {}
  RefcountInv == \A c \in Cowns : refcount[c] >= 0
  MuteMapInv == \A m \in muted : m \in UNION Range(mute_map)
  TypeInvariant == MutedInv /\ UnmutableInv /\ RefcountInv /\ MuteMapInv

  RefcountDrop == <>[](\A c \in Cowns : refcount[c] = 0)
  WillUnmute ==
    []<>(\A k \in DOMAIN mute_map : mute_map[k] = {} \/ k \in overloaded)
  TemporalProp == RefcountDrop /\ WillUnmute

  ZeroRC(c) == rc_barrier = BehaviourCount /\ refcount[c] = 0
  TriggersUnmute(mutor) == mutor \in overloaded \/ ZeroRC(mutor)
end define;

fair process behaviour \in 1..BehaviourCount
variables
  required \in Subsets(Cowns, 0, 3),
  next, acquired = {}, mutor, muting = {}, unmute_set
begin
Send:
  refcount :=
    [c \in Cowns |-> IF c \in required THEN refcount[c] + 1 ELSE refcount[c]];
  rc_barrier := rc_barrier + 1;
  \* Empty required set used to represent fewer behaviours in the system.
  if required = {} then goto Done; end if;

Unmute:
  while (\E r \in required : r \notin unmutable)
    /\ (overloaded \intersect required /= {})
  do
    next := Min({r \in required : r \notin unmutable});
    unmutable := unmutable \union {next};
    if next \in muted then
      muted := muted \ {next};
      available := available \union {next};
    end if;
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
  assert acquired \intersect muted = {};
  if (overloaded /= {}) /\ (acquired \intersect overloaded = {}) then
    either
      with mutor_ \in overloaded do mutor := mutor_ end with;
      muting := acquired \ unmutable;
    or
      skip;
    end either;
  end if;

Complete:
  \* Arbitrarily toggle overloaded state of some acquired cowns.
  with overloading \in Subsets(acquired \ muting, 0, 3) do
    with unoverloading \in Subsets(acquired \intersect overloaded, 0, 3) do
      overloaded := (overloaded \union overloading) \ unoverloading;
    end with;
  end with;

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

MuteMapScan:
  unmute_set :=
    UNION Range([c \in {k \in Cowns : TriggersUnmute(k)} |-> mute_map[c]]);
  mute_map := [c \in Cowns |-> IF TriggersUnmute(c) THEN {} ELSE mute_map[c]];
  muted := muted \ unmute_set;
  available := available \union unmute_set;
end process;

end algorithm; *)

\* BEGIN TRANSLATION - the hash of the PCal code: PCal-bc8e2f6d1cef2a2ee2ced52555aa4e69
CONSTANT defaultInitValue
VARIABLES available, overloaded, muted, unmutable, mute_map, refcount,
          rc_barrier, pc

(* define statement *)
BehaviourCount == 3

MutedInv == available \intersect muted = {}

UnmutableInv == overloaded \intersect muted = {}
RefcountInv == \A c \in Cowns : refcount[c] >= 0
MuteMapInv == \A m \in muted : m \in UNION Range(mute_map)
TypeInvariant == MutedInv /\ UnmutableInv /\ RefcountInv /\ MuteMapInv

RefcountDrop == <>[](\A c \in Cowns : refcount[c] = 0)
WillUnmute ==
  []<>(\A k \in DOMAIN mute_map : mute_map[k] = {} \/ k \in overloaded)
TemporalProp == RefcountDrop /\ WillUnmute

ZeroRC(c) == rc_barrier = BehaviourCount /\ refcount[c] = 0
TriggersUnmute(mutor) == mutor \in overloaded \/ ZeroRC(mutor)

VARIABLES required, next, acquired, mutor, muting, unmute_set

vars == << available, overloaded, muted, unmutable, mute_map, refcount,
           rc_barrier, pc, required, next, acquired, mutor, muting,
           unmute_set >>

ProcSet == (1..BehaviourCount)

Init == (* Global variables *)
        /\ available = Cowns
        /\ overloaded = {}
        /\ muted = {}
        /\ unmutable = {}
        /\ mute_map = [c \in Cowns |-> {}]
        /\ refcount = [c \in Cowns |-> 0]
        /\ rc_barrier = 0
        (* Process behaviour *)
        /\ required \in [1..BehaviourCount -> Subsets(Cowns, 0, 3)]
        /\ next = [self \in 1..BehaviourCount |-> defaultInitValue]
        /\ acquired = [self \in 1..BehaviourCount |-> {}]
        /\ mutor = [self \in 1..BehaviourCount |-> defaultInitValue]
        /\ muting = [self \in 1..BehaviourCount |-> {}]
        /\ unmute_set = [self \in 1..BehaviourCount |-> defaultInitValue]
        /\ pc = [self \in ProcSet |-> "Send"]

Send(self) == /\ pc[self] = "Send"
              /\ refcount' = [c \in Cowns |-> IF c \in required[self] THEN refcount[c] + 1 ELSE refcount[c]]
              /\ rc_barrier' = rc_barrier + 1
              /\ IF required[self] = {}
                    THEN /\ pc' = [pc EXCEPT ![self] = "Done"]
                    ELSE /\ pc' = [pc EXCEPT ![self] = "Unmute"]
              /\ UNCHANGED << available, overloaded, muted, unmutable,
                              mute_map, required, next, acquired, mutor,
                              muting, unmute_set >>

Unmute(self) == /\ pc[self] = "Unmute"
                /\ IF     (\E r \in required[self] : r \notin unmutable)
                      /\ (overloaded \intersect required[self] /= {})
                      THEN /\ next' = [next EXCEPT ![self] = Min({r \in required[self] : r \notin unmutable})]
                           /\ unmutable' = (unmutable \union {next'[self]})
                           /\ IF next'[self] \in muted
                                 THEN /\ muted' = muted \ {next'[self]}
                                      /\ available' = (available \union {next'[self]})
                                 ELSE /\ TRUE
                                      /\ UNCHANGED << available, muted >>
                           /\ pc' = [pc EXCEPT ![self] = "Unmute"]
                      ELSE /\ pc' = [pc EXCEPT ![self] = "Acquire"]
                           /\ UNCHANGED << available, muted, unmutable, next >>
                /\ UNCHANGED << overloaded, mute_map, refcount, rc_barrier,
                                required, acquired, mutor, muting, unmute_set >>

Acquire(self) == /\ pc[self] = "Acquire"
                 /\ IF required[self] /= {}
                       THEN /\ next' = [next EXCEPT ![self] = Min(required[self])]
                            /\ next'[self] \in available
                            /\ acquired' = [acquired EXCEPT ![self] = acquired[self] \union {next'[self]}]
                            /\ required' = [required EXCEPT ![self] = required[self] \ {next'[self]}]
                            /\ available' = available \ {next'[self]}
                            /\ pc' = [pc EXCEPT ![self] = "Acquire"]
                       ELSE /\ pc' = [pc EXCEPT ![self] = "Action"]
                            /\ UNCHANGED << available, required, next,
                                            acquired >>
                 /\ UNCHANGED << overloaded, muted, unmutable, mute_map,
                                 refcount, rc_barrier, mutor, muting,
                                 unmute_set >>

Action(self) == /\ pc[self] = "Action"
                /\ Assert(required[self] = {},
                          "Failure of assertion at line 78, column 3.")
                /\ Assert(acquired[self] \intersect muted = {},
                          "Failure of assertion at line 79, column 3.")
                /\ IF (overloaded /= {}) /\ (acquired[self] \intersect overloaded = {})
                      THEN /\ \/ /\ \E mutor_ \in overloaded:
                                      mutor' = [mutor EXCEPT ![self] = mutor_]
                                 /\ muting' = [muting EXCEPT ![self] = acquired[self] \ unmutable]
                              \/ /\ TRUE
                                 /\ UNCHANGED <<mutor, muting>>
                      ELSE /\ TRUE
                           /\ UNCHANGED << mutor, muting >>
                /\ pc' = [pc EXCEPT ![self] = "Complete"]
                /\ UNCHANGED << available, overloaded, muted, unmutable,
                                mute_map, refcount, rc_barrier, required, next,
                                acquired, unmute_set >>

Complete(self) == /\ pc[self] = "Complete"
                  /\ \E overloading \in Subsets(acquired[self] \ muting[self], 0, 3):
                       \E unoverloading \in Subsets(acquired[self] \intersect overloaded, 0, 3):
                         overloaded' = (overloaded \union overloading) \ unoverloading
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
                            "Failure of assertion at line 107, column 3.")
                  /\ pc' = [pc EXCEPT ![self] = "MuteMapScan"]
                  /\ UNCHANGED << unmutable, rc_barrier, required, next, mutor,
                                  unmute_set >>

MuteMapScan(self) == /\ pc[self] = "MuteMapScan"
                     /\ unmute_set' = [unmute_set EXCEPT ![self] = UNION Range([c \in {k \in Cowns : TriggersUnmute(k)} |-> mute_map[c]])]
                     /\ mute_map' = [c \in Cowns |-> IF TriggersUnmute(c) THEN {} ELSE mute_map[c]]
                     /\ muted' = muted \ unmute_set'[self]
                     /\ available' = (available \union unmute_set'[self])
                     /\ pc' = [pc EXCEPT ![self] = "Done"]
                     /\ UNCHANGED << overloaded, unmutable, refcount,
                                     rc_barrier, required, next, acquired,
                                     mutor, muting >>

behaviour(self) == Send(self) \/ Unmute(self) \/ Acquire(self)
                      \/ Action(self) \/ Complete(self)
                      \/ MuteMapScan(self)

(* Allow infinite stuttering to prevent deadlock on termination. *)
Terminating == /\ \A self \in ProcSet: pc[self] = "Done"
               /\ UNCHANGED vars

Next == (\E self \in 1..BehaviourCount: behaviour(self))
           \/ Terminating

Spec == /\ Init /\ [][Next]_vars
        /\ \A self \in 1..BehaviourCount : WF_vars(behaviour(self))

Termination == <>(\A self \in ProcSet: pc[self] = "Done")

\* END TRANSLATION - the hash of the generated TLA code (remove to silence divergence warnings): TLA-bd24460ac3e3dbc5294ac3189bb484af

====
