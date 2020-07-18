---- MODULE backpressure ----

\* pcal backpressure.tla && TLA_JAVA=/usr/lib/jvm/java-14-openjdk/bin/java tlc backpressure.tla -workers 8

\* Note: Each while iteration is an atomic step.

EXTENDS TLC, Integers, FiniteSets

Cowns == 1..3

Subsets(s, min, max) ==
  {cs \in SUBSET s : Cardinality(cs) >= min /\ Cardinality(cs) <= max}

Min(s) == CHOOSE x \in s: \A y \in s \ {x}: y > x

(* --algorithm backpressure

variables
  available = Cowns,
  overloaded = {},
  muted = {},
  unmutable = {},
  mute_map = [c \in Cowns |-> {}];

define
end define;

fair process behaviour \in 1..3 \* TODO: more
variables
  required \in Subsets(Cowns, 1, 3), next, acquired = {}, muting = {}
begin
  Send:
    skip;
  Unmute:
    while (required \cap muted) /= {} do
      next := Min(required \cap muted);
      muted := muted \ {next};
      available := available \union {next};
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
        with mutor \in overloaded do
          muting := (acquired \ unmutable);
          mute_map[mutor] := mute_map[mutor] \union muting;
        end with;
      or
        skip;
      end either;
    end if;
  Complete:
    muted := muted \union muting;
    available := available \union (acquired \ muting);
    acquired := {};
    assert acquired \union required = {};
end process;

end algorithm; *)

\* BEGIN TRANSLATION - the hash of the PCal code: PCal-75d87bb2e4ce7f600ed3360c12368236
CONSTANT defaultInitValue
VARIABLES available, overloaded, muted, unmutable, mute_map, pc, required,
          next, acquired, muting

vars == << available, overloaded, muted, unmutable, mute_map, pc, required,
           next, acquired, muting >>

ProcSet == (1..3)

Init == (* Global variables *)
        /\ available = Cowns
        /\ overloaded = {}
        /\ muted = {}
        /\ unmutable = {}
        /\ mute_map = [c \in Cowns |-> {}]
        (* Process behaviour *)
        /\ required \in [1..3 -> Subsets(Cowns, 1, 3)]
        /\ next = [self \in 1..3 |-> defaultInitValue]
        /\ acquired = [self \in 1..3 |-> {}]
        /\ muting = [self \in 1..3 |-> {}]
        /\ pc = [self \in ProcSet |-> "Send"]

Send(self) == /\ pc[self] = "Send"
              /\ TRUE
              /\ pc' = [pc EXCEPT ![self] = "Unmute"]
              /\ UNCHANGED << available, overloaded, muted, unmutable,
                              mute_map, required, next, acquired, muting >>

Unmute(self) == /\ pc[self] = "Unmute"
                /\ IF (required[self] \cap muted) /= {}
                      THEN /\ next' = [next EXCEPT ![self] = Min(required[self] \cap muted)]
                           /\ muted' = muted \ {next'[self]}
                           /\ available' = (available \union {next'[self]})
                           /\ unmutable' = (unmutable \union {next'[self]})
                           /\ pc' = [pc EXCEPT ![self] = "Unmute"]
                      ELSE /\ pc' = [pc EXCEPT ![self] = "Acquire"]
                           /\ UNCHANGED << available, muted, unmutable, next >>
                /\ UNCHANGED << overloaded, mute_map, required, acquired,
                                muting >>

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
                                 muting >>

Action(self) == /\ pc[self] = "Action"
                /\ Assert(required[self] = {},
                          "Failure of assertion at line 51, column 5.")
                /\ \E overloading \in Subsets(acquired[self] \ muted, 0, 3):
                     overloaded' = (overloaded \union overloading)
                /\ IF (overloaded' /= {}) /\ (acquired[self] \cap overloaded' = {})
                      THEN /\ \/ /\ \E mutor \in overloaded':
                                      /\ muting' = [muting EXCEPT ![self] = (acquired[self] \ unmutable)]
                                      /\ mute_map' = [mute_map EXCEPT ![mutor] = mute_map[mutor] \union muting'[self]]
                              \/ /\ TRUE
                                 /\ UNCHANGED <<mute_map, muting>>
                      ELSE /\ TRUE
                           /\ UNCHANGED << mute_map, muting >>
                /\ pc' = [pc EXCEPT ![self] = "Complete"]
                /\ UNCHANGED << available, muted, unmutable, required, next,
                                acquired >>

Complete(self) == /\ pc[self] = "Complete"
                  /\ muted' = (muted \union muting[self])
                  /\ available' = (available \union (acquired[self] \ muting[self]))
                  /\ acquired' = [acquired EXCEPT ![self] = {}]
                  /\ Assert(acquired'[self] \union required[self] = {},
                            "Failure of assertion at line 69, column 5.")
                  /\ pc' = [pc EXCEPT ![self] = "Done"]
                  /\ UNCHANGED << overloaded, unmutable, mute_map, required,
                                  next, muting >>

behaviour(self) == Send(self) \/ Unmute(self) \/ Acquire(self)
                      \/ Action(self) \/ Complete(self)

(* Allow infinite stuttering to prevent deadlock on termination. *)
Terminating == /\ \A self \in ProcSet: pc[self] = "Done"
               /\ UNCHANGED vars

Next == (\E self \in 1..3: behaviour(self))
           \/ Terminating

Spec == /\ Init /\ [][Next]_vars
        /\ \A self \in 1..3 : WF_vars(behaviour(self))

Termination == <>(\A self \in ProcSet: pc[self] = "Done")

\* END TRANSLATION - the hash of the generated TLA code (remove to silence divergence warnings): TLA-dba85418301e715feb75bea1c056a466

\* Correctness == []<>(muted_cowns = {})

MuteSetInv == \A k \in DOMAIN mute_map : (mute_map[k] = {}) \/ (k \in overloaded)
MutedInv == available \intersect muted = {}
UnmutableInv == (overloaded \union unmutable) \cap muted = {}

TypeCorrect == MuteSetInv /\ MutedInv /\ UnmutableInv

====
