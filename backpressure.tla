---- MODULE backpressure ----

EXTENDS FiniteSets, Naturals, TLC

Cowns == 1..3
Behaviours == 1..3

Min(xs) == CHOOSE x \in xs: \A y \in xs: x <= y

(* --algorithm backpressure

variables
  \* Mapping of behaviour to required cown
  required = [b \in Behaviours |-> {}],
  \* Mapping of behaviour to acquired cown
  acquired = [b \in Behaviours |-> {}],
  \* Cowns available for running behaviours
  available = Cowns,
  \* Cowns that are unavailable
  unavailable = {},
  \* Cowns that are overloaded
  overloaded = {},
  \* Mapping of mutor to unavailable
  mute_map = [c \in Cowns |-> {}],

define
  \* unavailable cowns must not be available, overloaded, or protected.
  UnavailableInv == (unavailable \intersect (available \union overloaded)) = {}
  \* All unavailable cowns must exist in at least one mute map entry.
  MuteMapInv == \A m \in unavailable : \E c \in Cowns : m \in mute_map[c]
  \* This does not hold
  ReverseInv == \A c \in Cowns: mute_map[c] \subseteq unavailable

  \* All invalid mute map entries will eventually be removed.
  MuteMapProp ==
    []<>(\A k \in DOMAIN mute_map: mute_map[k] = {} \/ k \in overloaded)
end define;

fair process behaviour \in Behaviours
variables
  cowns \in SUBSET Cowns,
begin
Create:
  \* Create a behaviour that requires cowns
  required[self] := cowns;

Acquire:
  \* Acquire the cowns
  while required[self] /= {} do
    with next = Min(required[self]) do
      await (next \in available) \/ (\E c \in (required[self] \union acquired[self]): c \in overloaded /\ next \in (available \union unavailable));
      unavailable := unavailable \ {next};
      available := available \ {next};
      required[self] := required[self] \ {next};
      acquired[self] := acquired[self] \union {next};
    end with;
  end while;
  
Action:
  \* Any cowns cown may toggle their overloaded state when the behaviour completes.
  with overload \in SUBSET acquired[self],
       unoverload \in SUBSET ((acquired[self] \ overload) \intersect overloaded),
       unmute = UNION {mute_map[c] : c \in unoverload}
  do
    overloaded := (overloaded \ unoverload) \union overload;
  
    either
      \* No new behaviour is created
      unavailable := unavailable \ unmute;
      available := available \union acquired[self] \union unmute;
      mute_map := [m \in unoverload |-> {} ] @@ mute_map;
    or   
      with receiver \in Cowns, mute = acquired[self] \ (acquired[self] \intersect overloaded) do
        \* Mute senders if the receiver triggers muting and the receiver isn't one of the senders.
        if receiver \in ((overloaded \union unavailable) \ acquired[self]) /\ (\E b \in Behaviours: receiver \in required[b]) then
          \* Add muted senders to the mute map entry for the receiver.
          unavailable := (unavailable \union mute) \ unmute;
          available := available \union (acquired[self] \ mute) \union unmute;
          mute_map := (receiver :> mute_map[receiver] \union mute) @@ [m \in unoverload |-> {} ] @@ mute_map;
        else      
          \* Senders are not muted, so all become available.
          unavailable := unavailable \ unmute;
          available := available \union acquired[self] \union unmute;
          mute_map := [m \in unoverload |-> {} ] @@ mute_map;
        end if;
      end with;
    end either;
  end with;
  
  acquired[self] := {}
end process;

end algorithm; *)
\* BEGIN TRANSLATION - the hash of the PCal code: PCal-20c7b9098722df5f690cfcfa6f6b90d9
VARIABLES required, acquired, available, unavailable, overloaded, mute_map, 
          pc

(* define statement *)
UnavailableInv == (unavailable \intersect (available \union overloaded)) = {}

MuteMapInv == \A m \in unavailable : \E c \in Cowns : m \in mute_map[c]

ReverseInv == \A c \in Cowns: mute_map[c] \subseteq unavailable


MuteMapProp ==
  []<>(\A k \in DOMAIN mute_map: mute_map[k] = {} \/ k \in overloaded)

VARIABLE cowns

vars == << required, acquired, available, unavailable, overloaded, mute_map, 
           pc, cowns >>

ProcSet == (Behaviours)

Init == (* Global variables *)
        /\ required = [b \in Behaviours |-> {}]
        /\ acquired = [b \in Behaviours |-> {}]
        /\ available = Cowns
        /\ unavailable = {}
        /\ overloaded = {}
        /\ mute_map = [c \in Cowns |-> {}]
        (* Process behaviour *)
        /\ cowns \in [Behaviours -> SUBSET Cowns]
        /\ pc = [self \in ProcSet |-> "Create"]

Create(self) == /\ pc[self] = "Create"
                /\ required' = [required EXCEPT ![self] = cowns[self]]
                /\ pc' = [pc EXCEPT ![self] = "Acquire"]
                /\ UNCHANGED << acquired, available, unavailable, overloaded, 
                                mute_map, cowns >>

Acquire(self) == /\ pc[self] = "Acquire"
                 /\ IF required[self] /= {}
                       THEN /\ LET next == Min(required[self]) IN
                                 /\ (next \in available) \/ (\E c \in (required[self] \union acquired[self]): c \in overloaded /\ next \in (available \union unavailable))
                                 /\ unavailable' = unavailable \ {next}
                                 /\ available' = available \ {next}
                                 /\ required' = [required EXCEPT ![self] = required[self] \ {next}]
                                 /\ acquired' = [acquired EXCEPT ![self] = acquired[self] \union {next}]
                            /\ pc' = [pc EXCEPT ![self] = "Acquire"]
                       ELSE /\ pc' = [pc EXCEPT ![self] = "Action"]
                            /\ UNCHANGED << required, acquired, available, 
                                            unavailable >>
                 /\ UNCHANGED << overloaded, mute_map, cowns >>

Action(self) == /\ pc[self] = "Action"
                /\ \E overload \in SUBSET acquired[self]:
                     \E unoverload \in SUBSET ((acquired[self] \ overload) \intersect overloaded):
                       LET unmute == UNION {mute_map[c] : c \in unoverload} IN
                         /\ overloaded' = ((overloaded \ unoverload) \union overload)
                         /\ \/ /\ unavailable' = unavailable \ unmute
                               /\ available' = (available \union acquired[self] \union unmute)
                               /\ mute_map' = [m \in unoverload |-> {} ] @@ mute_map
                            \/ /\ \E receiver \in Cowns:
                                    LET mute == acquired[self] \ (acquired[self] \intersect overloaded') IN
                                      IF receiver \in ((overloaded' \union unavailable) \ acquired[self]) /\ (\E b \in Behaviours: receiver \in required[b])
                                         THEN /\ unavailable' = (unavailable \union mute) \ unmute
                                              /\ available' = (available \union (acquired[self] \ mute) \union unmute)
                                              /\ mute_map' = (receiver :> mute_map[receiver] \union mute) @@ [m \in unoverload |-> {} ] @@ mute_map
                                         ELSE /\ unavailable' = unavailable \ unmute
                                              /\ available' = (available \union acquired[self] \union unmute)
                                              /\ mute_map' = [m \in unoverload |-> {} ] @@ mute_map
                /\ acquired' = [acquired EXCEPT ![self] = {}]
                /\ pc' = [pc EXCEPT ![self] = "Done"]
                /\ UNCHANGED << required, cowns >>

behaviour(self) == Create(self) \/ Acquire(self) \/ Action(self)

(* Allow infinite stuttering to prevent deadlock on termination. *)
Terminating == /\ \A self \in ProcSet: pc[self] = "Done"
               /\ UNCHANGED vars

Next == (\E self \in Behaviours: behaviour(self))
           \/ Terminating

Spec == /\ Init /\ [][Next]_vars
        /\ \A self \in Behaviours : WF_vars(behaviour(self))

Termination == <>(\A self \in ProcSet: pc[self] = "Done")

\* END TRANSLATION - the hash of the generated TLA code (remove to silence divergence warnings): TLA-a49e78ef3e424a25d8ba9014316fb7ca

====

(* TODO in `RunStep`:

The contition `(next \in unavailable) /\ (\E c \in required: HasPriority(c))` is used
to ensure that unavailable cowns never indefinetly prevent a behaviour, scheduled on an
overloaded cown, from running. Removing this condition from the `await` will
result in the `Termination` property failing. The `Termination` property is used
to check that all behaviours eventually run to completion.

One of the following should be done:
  1. The model should be modified to support `Termination` in a way that can be
     implemented without unacceptable overhead.

  2. The `Termination` property should be replaced by a weaker property, or
     there should be another way to model that unavailable cowns are eventually
     ununavailable. The property implemented in Verona currently is that any
     behaviour requiring a cown that is overloaded on creation of the behaviour
     will not prevent the behaviour from running. So the following example
     remains an issue:
      ```
      Cown 1 is unavailable. Behaviour `a` requires {2}. Behaviour `b` requires {1,2}.
      - `b`: `Protect`: 1 and 2 have no priority, nothing is protected.
      - `a`: `Action`: overload 2.
      - `b`: `AcquireNext`: await 1 becoming available, but 1 is unavailable.
      ```

*)
