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

Cowns == 1..2
Behaviours == 1..3

Range(f) == {f[x] : x \in DOMAIN f}
Min(s) == CHOOSE x \in s: \A y \in s \ {x}: y > x
Subsets(s, min, max) ==
  {cs \in SUBSET s : Cardinality(cs) >= min /\ Cardinality(cs) <= max}

(* --algorithm backpressure

variables
  available = Cowns,
  overloaded = {},
  muted = {},
  vital = {},
  mute_map = [c \in Cowns |-> {}],
  refcount = [c \in Cowns |-> 0],
  rc_barrier = 0;

define
  MutedInv == (available \union overloaded) \intersect muted = {}
  RefcountInv == \A c \in Cowns : refcount[c] >= 0
  MuteMapInv == \A m \in muted : m \in UNION Range(mute_map)
  TypeInvariant == MutedInv /\ RefcountInv /\ MuteMapInv

  RefcountDrop == <>[](\A c \in Cowns : refcount[c] = 0)
  WillUnmute ==
    []<>(\A k \in DOMAIN mute_map : mute_map[k] = {} \/ k \in overloaded)
  TemporalProp == RefcountDrop /\ WillUnmute

  IncRef(inc) == [c \in Cowns |-> IF c \in inc THEN refcount[c] + 1 ELSE refcount[c]]
  DecRef(dec) == [c \in Cowns |-> IF c \in dec THEN refcount[c] - 1 ELSE refcount[c]]
  TriggersUnmute(mutor) == mutor \notin overloaded \/ refcount[mutor] = 0
end define;

fair process behaviour \in Behaviours
variables
  required \in Subsets(Cowns, 0, 3),
  next, acquired = {}, mutor, muting = {}, unmute_set
begin
Create:
  refcount := IncRef(required);
  rc_barrier := rc_barrier + 1;
  \* Empty required set used to represent fewer behaviours in the system.
  if required = {} then goto Done; end if;

Barrier:
  await rc_barrier = Cardinality(Behaviours);

Unmute:
  while (\E r \in required : r \notin vital)
    /\ (overloaded \intersect required /= {})
  do
    next := Min({r \in required : r \notin vital});
    vital := vital \union {next};
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
      muting := acquired \ vital;
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
  refcount := DecRef(acquired);

MuteMapScan:
  unmute_set :=
    UNION Range([c \in {k \in Cowns : TriggersUnmute(k)} |-> mute_map[c]]);
  mute_map := [c \in Cowns |-> IF TriggersUnmute(c) THEN {} ELSE mute_map[c]];
  muted := muted \ unmute_set;
  available := available \union unmute_set;
end process;

end algorithm; *)

\* BEGIN TRANSLATION - the hash of the PCal code: PCal-cd6f0006745bb6e53a25a95c3d070d60
CONSTANT defaultInitValue
VARIABLES available, overloaded, muted, vital, mute_map, refcount, rc_barrier, 
          pc

(* define statement *)
MutedInv == (available \union overloaded) \intersect muted = {}
RefcountInv == \A c \in Cowns : refcount[c] >= 0
MuteMapInv == \A m \in muted : m \in UNION Range(mute_map)
TypeInvariant == MutedInv /\ RefcountInv /\ MuteMapInv

RefcountDrop == <>[](\A c \in Cowns : refcount[c] = 0)
WillUnmute ==
  []<>(\A k \in DOMAIN mute_map : mute_map[k] = {} \/ k \in overloaded)
TemporalProp == RefcountDrop /\ WillUnmute

IncRef(inc) == [c \in Cowns |-> IF c \in inc THEN refcount[c] + 1 ELSE refcount[c]]
DecRef(dec) == [c \in Cowns |-> IF c \in dec THEN refcount[c] - 1 ELSE refcount[c]]
TriggersUnmute(mutor) == mutor \notin overloaded \/ refcount[mutor] = 0

VARIABLES required, next, acquired, mutor, muting, unmute_set

vars == << available, overloaded, muted, vital, mute_map, refcount, 
           rc_barrier, pc, required, next, acquired, mutor, muting, 
           unmute_set >>

ProcSet == (Behaviours)

Init == (* Global variables *)
        /\ available = Cowns
        /\ overloaded = {}
        /\ muted = {}
        /\ vital = {}
        /\ mute_map = [c \in Cowns |-> {}]
        /\ refcount = [c \in Cowns |-> 0]
        /\ rc_barrier = 0
        (* Process behaviour *)
        /\ required \in [Behaviours -> Subsets(Cowns, 0, 3)]
        /\ next = [self \in Behaviours |-> defaultInitValue]
        /\ acquired = [self \in Behaviours |-> {}]
        /\ mutor = [self \in Behaviours |-> defaultInitValue]
        /\ muting = [self \in Behaviours |-> {}]
        /\ unmute_set = [self \in Behaviours |-> defaultInitValue]
        /\ pc = [self \in ProcSet |-> "Create"]

Create(self) == /\ pc[self] = "Create"
                /\ refcount' = IncRef(required[self])
                /\ rc_barrier' = rc_barrier + 1
                /\ IF required[self] = {}
                      THEN /\ pc' = [pc EXCEPT ![self] = "Done"]
                      ELSE /\ pc' = [pc EXCEPT ![self] = "Barrier"]
                /\ UNCHANGED << available, overloaded, muted, vital, mute_map, 
                                required, next, acquired, mutor, muting, 
                                unmute_set >>

Barrier(self) == /\ pc[self] = "Barrier"
                 /\ rc_barrier = Cardinality(Behaviours)
                 /\ pc' = [pc EXCEPT ![self] = "Unmute"]
                 /\ UNCHANGED << available, overloaded, muted, vital, mute_map, 
                                 refcount, rc_barrier, required, next, 
                                 acquired, mutor, muting, unmute_set >>

Unmute(self) == /\ pc[self] = "Unmute"
                /\ IF     (\E r \in required[self] : r \notin vital)
                      /\ (overloaded \intersect required[self] /= {})
                      THEN /\ next' = [next EXCEPT ![self] = Min({r \in required[self] : r \notin vital})]
                           /\ vital' = (vital \union {next'[self]})
                           /\ IF next'[self] \in muted
                                 THEN /\ muted' = muted \ {next'[self]}
                                      /\ available' = (available \union {next'[self]})
                                 ELSE /\ TRUE
                                      /\ UNCHANGED << available, muted >>
                           /\ pc' = [pc EXCEPT ![self] = "Unmute"]
                      ELSE /\ pc' = [pc EXCEPT ![self] = "Acquire"]
                           /\ UNCHANGED << available, muted, vital, next >>
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
                 /\ UNCHANGED << overloaded, muted, vital, mute_map, refcount, 
                                 rc_barrier, mutor, muting, unmute_set >>

Action(self) == /\ pc[self] = "Action"
                /\ Assert(required[self] = {}, 
                          "Failure of assertion at line 87, column 3.")
                /\ Assert(acquired[self] \intersect muted = {}, 
                          "Failure of assertion at line 88, column 3.")
                /\ IF (overloaded /= {}) /\ (acquired[self] \intersect overloaded = {})
                      THEN /\ \/ /\ \E mutor_ \in overloaded:
                                      mutor' = [mutor EXCEPT ![self] = mutor_]
                                 /\ muting' = [muting EXCEPT ![self] = acquired[self] \ vital]
                              \/ /\ TRUE
                                 /\ UNCHANGED <<mutor, muting>>
                      ELSE /\ TRUE
                           /\ UNCHANGED << mutor, muting >>
                /\ pc' = [pc EXCEPT ![self] = "Complete"]
                /\ UNCHANGED << available, overloaded, muted, vital, mute_map, 
                                refcount, rc_barrier, required, next, acquired, 
                                unmute_set >>

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
                  /\ refcount' = DecRef(acquired[self])
                  /\ pc' = [pc EXCEPT ![self] = "MuteMapScan"]
                  /\ UNCHANGED << vital, rc_barrier, required, next, acquired, 
                                  mutor, muting, unmute_set >>

MuteMapScan(self) == /\ pc[self] = "MuteMapScan"
                     /\ unmute_set' = [unmute_set EXCEPT ![self] = UNION Range([c \in {k \in Cowns : TriggersUnmute(k)} |-> mute_map[c]])]
                     /\ mute_map' = [c \in Cowns |-> IF TriggersUnmute(c) THEN {} ELSE mute_map[c]]
                     /\ muted' = muted \ unmute_set'[self]
                     /\ available' = (available \union unmute_set'[self])
                     /\ pc' = [pc EXCEPT ![self] = "Done"]
                     /\ UNCHANGED << overloaded, vital, refcount, rc_barrier, 
                                     required, next, acquired, mutor, muting >>

behaviour(self) == Create(self) \/ Barrier(self) \/ Unmute(self)
                      \/ Acquire(self) \/ Action(self) \/ Complete(self)
                      \/ MuteMapScan(self)

(* Allow infinite stuttering to prevent deadlock on termination. *)
Terminating == /\ \A self \in ProcSet: pc[self] = "Done"
               /\ UNCHANGED vars

Next == (\E self \in Behaviours: behaviour(self))
           \/ Terminating

Spec == /\ Init /\ [][Next]_vars
        /\ \A self \in Behaviours : WF_vars(behaviour(self))

Termination == <>(\A self \in ProcSet: pc[self] = "Done")

\* END TRANSLATION - the hash of the generated TLA code (remove to silence divergence warnings): TLA-5904c1e3b19ce45c5615663400cfcba1

====
