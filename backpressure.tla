---- MODULE backpressure ----

\* pcal backpressure.tla && tlc backpressure.tla

EXTENDS TLC, Integers, FiniteSets

Cowns == 1..3

RequiredSets ==
  {cs \in SUBSET Cowns : Cardinality(cs) >= 1 /\ Cardinality(cs) <= 3}

Min(s) == CHOOSE x \in s: \A y \in s \ {x}: y > x

(* --algorithm backpressure

variables
  available_cowns = Cowns,
  muted_cowns = {},
  unmutable_cowns = {};

fair process behaviour \in 1..3
variables required, acquired = {}, next, muted = {}
begin
  Send:
    with r \in RequiredSets do required := r; end with;
  Acquire:
    while required /= {} do
  AcquireCown:
      next := Min(required);
      await next \in available_cowns;
      acquired := acquired \union {next};
      required := required \ {next};
      available_cowns := available_cowns \ {next};
    end while;
  Complete:
    \* either
    \*   muted := acquired \ unmutable_cowns;
    \* or
    \*   skip;
    \* end either;
    available_cowns := available_cowns \union (acquired \ muted);
end process;

end algorithm; *)

\* BEGIN TRANSLATION - the hash of the PCal code: PCal-df0d6f1f9043b1c5065aeec74ab30cdf
CONSTANT defaultInitValue
VARIABLES available_cowns, muted_cowns, unmutable_cowns, pc, required, 
          acquired, next, muted

vars == << available_cowns, muted_cowns, unmutable_cowns, pc, required, 
           acquired, next, muted >>

ProcSet == (1..3)

Init == (* Global variables *)
        /\ available_cowns = Cowns
        /\ muted_cowns = {}
        /\ unmutable_cowns = {}
        (* Process behaviour *)
        /\ required = [self \in 1..3 |-> defaultInitValue]
        /\ acquired = [self \in 1..3 |-> {}]
        /\ next = [self \in 1..3 |-> defaultInitValue]
        /\ muted = [self \in 1..3 |-> {}]
        /\ pc = [self \in ProcSet |-> "Send"]

Send(self) == /\ pc[self] = "Send"
              /\ \E r \in RequiredSets:
                   required' = [required EXCEPT ![self] = r]
              /\ pc' = [pc EXCEPT ![self] = "Acquire"]
              /\ UNCHANGED << available_cowns, muted_cowns, unmutable_cowns, 
                              acquired, next, muted >>

Acquire(self) == /\ pc[self] = "Acquire"
                 /\ IF required[self] /= {}
                       THEN /\ pc' = [pc EXCEPT ![self] = "AcquireCown"]
                       ELSE /\ pc' = [pc EXCEPT ![self] = "Complete"]
                 /\ UNCHANGED << available_cowns, muted_cowns, unmutable_cowns, 
                                 required, acquired, next, muted >>

AcquireCown(self) == /\ pc[self] = "AcquireCown"
                     /\ next' = [next EXCEPT ![self] = Min(required[self])]
                     /\ next'[self] \in available_cowns
                     /\ acquired' = [acquired EXCEPT ![self] = acquired[self] \union {next'[self]}]
                     /\ required' = [required EXCEPT ![self] = required[self] \ {next'[self]}]
                     /\ available_cowns' = available_cowns \ {next'[self]}
                     /\ pc' = [pc EXCEPT ![self] = "Acquire"]
                     /\ UNCHANGED << muted_cowns, unmutable_cowns, muted >>

Complete(self) == /\ pc[self] = "Complete"
                  /\ available_cowns' = (available_cowns \union (acquired[self] \ muted[self]))
                  /\ pc' = [pc EXCEPT ![self] = "Done"]
                  /\ UNCHANGED << muted_cowns, unmutable_cowns, required, 
                                  acquired, next, muted >>

behaviour(self) == Send(self) \/ Acquire(self) \/ AcquireCown(self)
                      \/ Complete(self)

(* Allow infinite stuttering to prevent deadlock on termination. *)
Terminating == /\ \A self \in ProcSet: pc[self] = "Done"
               /\ UNCHANGED vars

Next == (\E self \in 1..3: behaviour(self))
           \/ Terminating

Spec == /\ Init /\ [][Next]_vars
        /\ \A self \in 1..3 : WF_vars(behaviour(self))

Termination == <>(\A self \in ProcSet: pc[self] = "Done")

\* END TRANSLATION - the hash of the generated TLA code (remove to silence divergence warnings): TLA-ffbb8c90fd659365fe744307e520c0b0

\* MutedInvariant == available_cowns \intersect muted_cowns = {}
\* Correctness == []<>(muted_cowns = {})

====
