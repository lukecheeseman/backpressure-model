---- MODULE backpressure ----

\* pcal backpressure.tla && tlc backpressure.tla

\* Note: Each while iteration is an atomic step.

EXTENDS TLC, Integers, FiniteSets

Cowns == 1..3

Subsets(s, min, max) ==
  {cs \in SUBSET s : Cardinality(cs) >= min /\ Cardinality(cs) <= max}

Min(s) == CHOOSE x \in s: \A y \in s \ {x}: y > x

(* --algorithm backpressure

variables
  available_cowns = Cowns,
  overloaded_cowns = {},
  muted_cowns = {},
  unmutable_cowns = {};

fair process behaviour \in 1..3
variables required, next, acquired = {}, muted = {}
begin
  Send:
    with r \in Subsets(Cowns, 1, 3) do required := r; end with;
  Unmute:
    while (required \cap muted_cowns) /= {} do
      next := Min(required \cap muted_cowns);
      muted_cowns := muted_cowns \ {next};
      available_cowns := available_cowns \union {next};
      unmutable_cowns := unmutable_cowns \union {next};
    end while;
  Acquire:
    while required /= {} do
      next := Min(required);
      await next \in available_cowns;
      acquired := acquired \union {next};
      required := required \ {next};
      available_cowns := available_cowns \ {next};
    end while;
  Mute:
    with overloaded \in Subsets(acquired \ muted_cowns, 0, 3) do
      overloaded_cowns := overloaded_cowns \union overloaded;
    end with;
    if (overloaded_cowns /= {}) /\ (acquired \cap overloaded_cowns = {}) then
      either
        muted := acquired \ unmutable_cowns;
        muted_cowns := muted_cowns \union muted;
        assert (overloaded_cowns \cap muted_cowns) = {};
        assert (unmutable_cowns \cap muted_cowns) = {};
      or
        skip;
      end either;
    end if;
  Complete:
    available_cowns := available_cowns \union (acquired \ muted);
end process;

end algorithm; *)

\* BEGIN TRANSLATION - the hash of the PCal code: PCal-66d64d289cd670b6b51315fed258a20b
CONSTANT defaultInitValue
VARIABLES available_cowns, overloaded_cowns, muted_cowns, unmutable_cowns, pc, 
          required, next, acquired, muted

vars == << available_cowns, overloaded_cowns, muted_cowns, unmutable_cowns, 
           pc, required, next, acquired, muted >>

ProcSet == (1..3)

Init == (* Global variables *)
        /\ available_cowns = Cowns
        /\ overloaded_cowns = {}
        /\ muted_cowns = {}
        /\ unmutable_cowns = {}
        (* Process behaviour *)
        /\ required = [self \in 1..3 |-> defaultInitValue]
        /\ next = [self \in 1..3 |-> defaultInitValue]
        /\ acquired = [self \in 1..3 |-> {}]
        /\ muted = [self \in 1..3 |-> {}]
        /\ pc = [self \in ProcSet |-> "Send"]

Send(self) == /\ pc[self] = "Send"
              /\ \E r \in Subsets(Cowns, 1, 3):
                   required' = [required EXCEPT ![self] = r]
              /\ pc' = [pc EXCEPT ![self] = "Unmute"]
              /\ UNCHANGED << available_cowns, overloaded_cowns, muted_cowns, 
                              unmutable_cowns, next, acquired, muted >>

Unmute(self) == /\ pc[self] = "Unmute"
                /\ IF (required[self] \cap muted_cowns) /= {}
                      THEN /\ next' = [next EXCEPT ![self] = Min(required[self] \cap muted_cowns)]
                           /\ muted_cowns' = muted_cowns \ {next'[self]}
                           /\ available_cowns' = (available_cowns \union {next'[self]})
                           /\ unmutable_cowns' = (unmutable_cowns \union {next'[self]})
                           /\ pc' = [pc EXCEPT ![self] = "Unmute"]
                      ELSE /\ pc' = [pc EXCEPT ![self] = "Acquire"]
                           /\ UNCHANGED << available_cowns, muted_cowns, 
                                           unmutable_cowns, next >>
                /\ UNCHANGED << overloaded_cowns, required, acquired, muted >>

Acquire(self) == /\ pc[self] = "Acquire"
                 /\ IF required[self] /= {}
                       THEN /\ next' = [next EXCEPT ![self] = Min(required[self])]
                            /\ next'[self] \in available_cowns
                            /\ acquired' = [acquired EXCEPT ![self] = acquired[self] \union {next'[self]}]
                            /\ required' = [required EXCEPT ![self] = required[self] \ {next'[self]}]
                            /\ available_cowns' = available_cowns \ {next'[self]}
                            /\ pc' = [pc EXCEPT ![self] = "Acquire"]
                       ELSE /\ pc' = [pc EXCEPT ![self] = "Mute"]
                            /\ UNCHANGED << available_cowns, required, next, 
                                            acquired >>
                 /\ UNCHANGED << overloaded_cowns, muted_cowns, 
                                 unmutable_cowns, muted >>

Mute(self) == /\ pc[self] = "Mute"
              /\ \E overloaded \in Subsets(acquired[self] \ muted_cowns, 0, 3):
                   overloaded_cowns' = (overloaded_cowns \union overloaded)
              /\ IF (overloaded_cowns' /= {}) /\ (acquired[self] \cap overloaded_cowns' = {})
                    THEN /\ \/ /\ muted' = [muted EXCEPT ![self] = acquired[self] \ unmutable_cowns]
                               /\ muted_cowns' = (muted_cowns \union muted'[self])
                               /\ Assert((overloaded_cowns' \cap muted_cowns') = {}, 
                                         "Failure of assertion at line 52, column 9.")
                               /\ Assert((unmutable_cowns \cap muted_cowns') = {}, 
                                         "Failure of assertion at line 53, column 9.")
                            \/ /\ TRUE
                               /\ UNCHANGED <<muted_cowns, muted>>
                    ELSE /\ TRUE
                         /\ UNCHANGED << muted_cowns, muted >>
              /\ pc' = [pc EXCEPT ![self] = "Complete"]
              /\ UNCHANGED << available_cowns, unmutable_cowns, required, next, 
                              acquired >>

Complete(self) == /\ pc[self] = "Complete"
                  /\ available_cowns' = (available_cowns \union (acquired[self] \ muted[self]))
                  /\ pc' = [pc EXCEPT ![self] = "Done"]
                  /\ UNCHANGED << overloaded_cowns, muted_cowns, 
                                  unmutable_cowns, required, next, acquired, 
                                  muted >>

behaviour(self) == Send(self) \/ Unmute(self) \/ Acquire(self)
                      \/ Mute(self) \/ Complete(self)

(* Allow infinite stuttering to prevent deadlock on termination. *)
Terminating == /\ \A self \in ProcSet: pc[self] = "Done"
               /\ UNCHANGED vars

Next == (\E self \in 1..3: behaviour(self))
           \/ Terminating

Spec == /\ Init /\ [][Next]_vars
        /\ \A self \in 1..3 : WF_vars(behaviour(self))

Termination == <>(\A self \in ProcSet: pc[self] = "Done")

\* END TRANSLATION - the hash of the generated TLA code (remove to silence divergence warnings): TLA-a68b2c8ae57a78a352598f8bd76b6f98

\* MutedInvariant == available_cowns \intersect muted_cowns = {}
\* Correctness == []<>(muted_cowns = {})

====
