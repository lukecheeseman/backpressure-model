---- MODULE backpressure ----

(*
Assumptions:
  - Fairness (weakly fair behaviour process)
  - Cowns cannot become overloaded while muted.
  - Mute map entries will eventually be removed and unmuted.
    - Modeled by having overloaded cowns eventually become not overloaded.
*)

EXTENDS TLC, Integers, FiniteSets

CONSTANT null
Cowns == 1..3
Behaviours == 1..4

Range(f) == {f[x] : x \in DOMAIN f}
Min(s) == CHOOSE x \in s: \A y \in s \ {x}: y > x
Intersection(a, b) == a \intersect b /= {}
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
  MutedInv == ~Intersection(available \union overloaded, muted)
  UnmutableInv == ~Intersection(unmutable, muted)
  RefcountInv == \A c \in Cowns : refcount[c] >= 0
  MuteMapInv == \A m \in muted : m \in UNION Range(mute_map)
  TypeInvariant == MutedInv /\ UnmutableInv /\ RefcountInv /\ MuteMapInv

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
  acquired = {}, mutor = null,
begin
Create:
  refcount := IncRef(required);
  rc_barrier := rc_barrier + 1;
  \* Empty required set used to represent fewer behaviours in the system.
  if required = {} then goto Done; end if;

Acquire:
  with next = Min(required) do
    if Intersection(overloaded, acquired \union required) then
      \* Make unmutable and schedule
      unmutable := unmutable \union {next};
      muted := muted \ {next};
      available := available \union {next};
    else
      \* Acquire cown
      await next \in available;
      acquired := acquired \union {next};
      required := required \ {next};
      available := available \ {next};
    end if;
    if required /= {} then
      goto Acquire;
    end if;
  end with;

Action:
  assert ~Intersection(acquired, muted);
  if overloaded /= {} /\ ~Intersection(acquired, overloaded) then
    either
      with mutor_ \in overloaded do mutor := mutor_ end with;
    or
      skip;
    end either;
  end if;

Complete:
  with muting = IF mutor /= null THEN acquired \ unmutable ELSE {} do
    \* Arbitrarily toggle overloaded state of some acquired cowns.
    with overloading \in Subsets(acquired \ muting, 0, 3) do
      with unoverloading \in Subsets(acquired \intersect overloaded, 0, 3) do
        overloaded := (overloaded \union overloading) \ unoverloading;
      end with;
    end with;

    if mutor /= null then
      muted := muted \union muting;
      mute_map[mutor] := mute_map[mutor] \union muting;
    end if;
    available := available \union (acquired \ muting);
  end with;

  refcount := DecRef(acquired);

MuteMapScan:
  await rc_barrier = Cardinality(Behaviours);

  with unmuting = UNION Range([c \in {k \in Cowns : TriggersUnmute(k)} |-> mute_map[c]]) do
    mute_map := [c \in Cowns |-> IF TriggersUnmute(c) THEN {} ELSE mute_map[c]];
    muted := muted \ unmuting;
    available := available \union unmuting;
  end with;
end process;

end algorithm; *)

\* BEGIN TRANSLATION - the hash of the PCal code: PCal-e24769338b2b389a4c531bac67f11afb
VARIABLES available, overloaded, muted, unmutable, mute_map, refcount, 
          rc_barrier, pc

(* define statement *)
MutedInv == ~Intersection(available \union overloaded, muted)
UnmutableInv == ~Intersection(unmutable, muted)
RefcountInv == \A c \in Cowns : refcount[c] >= 0
MuteMapInv == \A m \in muted : m \in UNION Range(mute_map)
TypeInvariant == MutedInv /\ UnmutableInv /\ RefcountInv /\ MuteMapInv

RefcountDrop == <>[](\A c \in Cowns : refcount[c] = 0)
WillUnmute ==
  []<>(\A k \in DOMAIN mute_map : mute_map[k] = {} \/ k \in overloaded)
TemporalProp == RefcountDrop /\ WillUnmute

IncRef(inc) == [c \in Cowns |-> IF c \in inc THEN refcount[c] + 1 ELSE refcount[c]]
DecRef(dec) == [c \in Cowns |-> IF c \in dec THEN refcount[c] - 1 ELSE refcount[c]]
TriggersUnmute(mutor) == mutor \notin overloaded \/ refcount[mutor] = 0

VARIABLES required, acquired, mutor

vars == << available, overloaded, muted, unmutable, mute_map, refcount, 
           rc_barrier, pc, required, acquired, mutor >>

ProcSet == (Behaviours)

Init == (* Global variables *)
        /\ available = Cowns
        /\ overloaded = {}
        /\ muted = {}
        /\ unmutable = {}
        /\ mute_map = [c \in Cowns |-> {}]
        /\ refcount = [c \in Cowns |-> 0]
        /\ rc_barrier = 0
        (* Process behaviour *)
        /\ required \in [Behaviours -> Subsets(Cowns, 0, 3)]
        /\ acquired = [self \in Behaviours |-> {}]
        /\ mutor = [self \in Behaviours |-> null]
        /\ pc = [self \in ProcSet |-> "Create"]

Create(self) == /\ pc[self] = "Create"
                /\ refcount' = IncRef(required[self])
                /\ rc_barrier' = rc_barrier + 1
                /\ IF required[self] = {}
                      THEN /\ pc' = [pc EXCEPT ![self] = "Done"]
                      ELSE /\ pc' = [pc EXCEPT ![self] = "Acquire"]
                /\ UNCHANGED << available, overloaded, muted, unmutable, 
                                mute_map, required, acquired, mutor >>

Acquire(self) == /\ pc[self] = "Acquire"
                 /\ LET next == Min(required[self]) IN
                      /\ IF Intersection(overloaded, acquired[self] \union required[self])
                            THEN /\ unmutable' = (unmutable \union {next})
                                 /\ muted' = muted \ {next}
                                 /\ available' = (available \union {next})
                                 /\ UNCHANGED << required, acquired >>
                            ELSE /\ next \in available
                                 /\ acquired' = [acquired EXCEPT ![self] = acquired[self] \union {next}]
                                 /\ required' = [required EXCEPT ![self] = required[self] \ {next}]
                                 /\ available' = available \ {next}
                                 /\ UNCHANGED << muted, unmutable >>
                      /\ IF required'[self] /= {}
                            THEN /\ pc' = [pc EXCEPT ![self] = "Acquire"]
                            ELSE /\ pc' = [pc EXCEPT ![self] = "Action"]
                 /\ UNCHANGED << overloaded, mute_map, refcount, rc_barrier, 
                                 mutor >>

Action(self) == /\ pc[self] = "Action"
                /\ Assert(~Intersection(acquired[self], muted), 
                          "Failure of assertion at line 82, column 3.")
                /\ IF overloaded /= {} /\ ~Intersection(acquired[self], overloaded)
                      THEN /\ \/ /\ \E mutor_ \in overloaded:
                                      mutor' = [mutor EXCEPT ![self] = mutor_]
                              \/ /\ TRUE
                                 /\ mutor' = mutor
                      ELSE /\ TRUE
                           /\ mutor' = mutor
                /\ pc' = [pc EXCEPT ![self] = "Complete"]
                /\ UNCHANGED << available, overloaded, muted, unmutable, 
                                mute_map, refcount, rc_barrier, required, 
                                acquired >>

Complete(self) == /\ pc[self] = "Complete"
                  /\ LET muting == IF mutor[self] /= null THEN acquired[self] \ unmutable ELSE {} IN
                       /\ \E overloading \in Subsets(acquired[self] \ muting, 0, 3):
                            \E unoverloading \in Subsets(acquired[self] \intersect overloaded, 0, 3):
                              overloaded' = (overloaded \union overloading) \ unoverloading
                       /\ IF mutor[self] /= null
                             THEN /\ muted' = (muted \union muting)
                                  /\ mute_map' = [mute_map EXCEPT ![mutor[self]] = mute_map[mutor[self]] \union muting]
                             ELSE /\ TRUE
                                  /\ UNCHANGED << muted, mute_map >>
                       /\ available' = (available \union (acquired[self] \ muting))
                  /\ refcount' = DecRef(acquired[self])
                  /\ pc' = [pc EXCEPT ![self] = "MuteMapScan"]
                  /\ UNCHANGED << unmutable, rc_barrier, required, acquired, 
                                  mutor >>

MuteMapScan(self) == /\ pc[self] = "MuteMapScan"
                     /\ rc_barrier = Cardinality(Behaviours)
                     /\ LET unmuting == UNION Range([c \in {k \in Cowns : TriggersUnmute(k)} |-> mute_map[c]]) IN
                          /\ mute_map' = [c \in Cowns |-> IF TriggersUnmute(c) THEN {} ELSE mute_map[c]]
                          /\ muted' = muted \ unmuting
                          /\ available' = (available \union unmuting)
                     /\ pc' = [pc EXCEPT ![self] = "Done"]
                     /\ UNCHANGED << overloaded, unmutable, refcount, 
                                     rc_barrier, required, acquired, mutor >>

behaviour(self) == Create(self) \/ Acquire(self) \/ Action(self)
                      \/ Complete(self) \/ MuteMapScan(self)

(* Allow infinite stuttering to prevent deadlock on termination. *)
Terminating == /\ \A self \in ProcSet: pc[self] = "Done"
               /\ UNCHANGED vars

Next == (\E self \in Behaviours: behaviour(self))
           \/ Terminating

Spec == /\ Init /\ [][Next]_vars
        /\ \A self \in Behaviours : WF_vars(behaviour(self))

Termination == <>(\A self \in ProcSet: pc[self] = "Done")

\* END TRANSLATION - the hash of the generated TLA code (remove to silence divergence warnings): TLA-31975375dc47377a475d138091131e3c

====
