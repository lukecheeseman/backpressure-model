---- MODULE backpressure ----

\* pcal backpressure.tla && tlc backpressure.tla

EXTENDS TLC, Integers, FiniteSets

Cowns == 1..3
RequiredCowns ==
  {cs \in SUBSET Cowns : Cardinality(cs) >= 1 /\ Cardinality(cs) <= 3}

Min(s) == CHOOSE x \in s: \A y \in s \ {x}: y > x

(* --algorithm backpressure

variables
  available_cowns = Cowns,

fair process behaviour \in 1..3
variables required, acquired = {}, next
begin
  Send:
    with r \in RequiredCowns do required := r; end with;
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
    available_cowns := available_cowns \union acquired;

end process;

end algorithm; *)
\* BEGIN TRANSLATION - the hash of the PCal code: PCal-9a3f24469c1b8d0364121e5a10ce232e
CONSTANT defaultInitValue
VARIABLES available_cowns, pc, required, acquired, next

vars == << available_cowns, pc, required, acquired, next >>

ProcSet == (1..3)

Init == (* Global variables *)
        /\ available_cowns = Cowns
        (* Process behaviour *)
        /\ required = [self \in 1..3 |-> defaultInitValue]
        /\ acquired = [self \in 1..3 |-> {}]
        /\ next = [self \in 1..3 |-> defaultInitValue]
        /\ pc = [self \in ProcSet |-> "Send"]

Send(self) == /\ pc[self] = "Send"
              /\ \E r \in RequiredCowns:
                   required' = [required EXCEPT ![self] = r]
              /\ pc' = [pc EXCEPT ![self] = "Acquire"]
              /\ UNCHANGED << available_cowns, acquired, next >>

Acquire(self) == /\ pc[self] = "Acquire"
                 /\ IF required[self] /= {}
                       THEN /\ pc' = [pc EXCEPT ![self] = "AcquireCown"]
                       ELSE /\ pc' = [pc EXCEPT ![self] = "Complete"]
                 /\ UNCHANGED << available_cowns, required, acquired, next >>

AcquireCown(self) == /\ pc[self] = "AcquireCown"
                     /\ next' = [next EXCEPT ![self] = Min(required[self])]
                     /\ next'[self] \in available_cowns
                     /\ acquired' = [acquired EXCEPT ![self] = acquired[self] \union {next'[self]}]
                     /\ required' = [required EXCEPT ![self] = required[self] \ {next'[self]}]
                     /\ available_cowns' = available_cowns \ {next'[self]}
                     /\ pc' = [pc EXCEPT ![self] = "Acquire"]

Complete(self) == /\ pc[self] = "Complete"
                  /\ available_cowns' = (available_cowns \union acquired[self])
                  /\ pc' = [pc EXCEPT ![self] = "Done"]
                  /\ UNCHANGED << required, acquired, next >>

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

\* END TRANSLATION - the hash of the generated TLA code (remove to silence divergence warnings): TLA-e5dcf895eb082b556d4ab79b3c507573

\* MutedInvariant == available_cowns \intersect muted_cowns = {}
\* Correctness == []<>(muted_cowns = {})

====
