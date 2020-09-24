---- MODULE backpressure ----

EXTENDS FiniteSets, Naturals, TLC

Cowns == 1..3
Behaviours == 1..3

Min(xs) == CHOOSE x \in xs: \A y \in xs: x <= y
Range(f) == { f[x] : x \in DOMAIN f }

(* --algorithm backpressure

variables
  \* Cowns available for running behaviours
  available = Cowns,
  \* Mapping of mutor to unavailable
  mute_map = [c \in Cowns |-> {}],
  \* Mapping of behaviour to required cown
  required = [b \in Behaviours |-> {}],
  \* Mapping of behaviour to acquired cown
  acquired = [b \in Behaviours |-> {}],
  \* Mapping of behaviour to muting cown
  gobble = [b \in Behaviours |-> 0],
  
  \* Cowns that are overloaded
  overloaded = {},

define
  \* unavailable cowns must not be available, overloaded, or protected.
  UnavailableInv == ((UNION Range(mute_map)) \intersect (available \union overloaded)) = {}
  \* All muting cowns must be overloaded
  OverloadedInv == \A c \in DOMAIN mute_map : mute_map[c] /= {} => c \in overloaded
  \* A cown cannot be muted by multiple cowns
  DisjointMuteMapImageInv == \A c \in Cowns, co \in Cowns: c /= co => mute_map[c] \intersect mute_map[co] = {}

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
      await (next \in available) \/ (\E c \in (required[self] \union acquired[self]): c \in overloaded /\ next \in UNION Range(mute_map));
      if (next \in available) then
        available := available \ {next};
        required[self] := required[self] \ {next};
        acquired[self] := acquired[self] \union {next};
      else
        assert (\E c \in (required[self] \union acquired[self]): c \in overloaded /\ next \in UNION Range(mute_map));
        with c = CHOOSE c \in Cowns: next \in mute_map[c] do
          mute_map[c] := mute_map[c] \ {next};
          available := available \union {next};
        end with;
      end if;
    end with;
  end while;
  
Send:
  either
    \* No new behaviour is created
    skip;
  or   
    with receiver \in Cowns, mute = acquired[self] \ overloaded do
      \* Mute senders if the receiver triggers muting and the receiver isn't one of the senders.
      if (receiver \in (overloaded \union UNION Range(mute_map)) \ acquired[self]) /\ (\E b \in Behaviours: receiver \in required[b]) then
        \* Add muted senders to the mute map entry for the receiver.
        gobble[self] := receiver;
      else      
        \* Senders are not muted, so all become available.
        skip;
      end if;
    end with;
  end either;

Terminate:
  \* Any cowns cown may toggle their overloaded state when the behaviour completes.
  with overload \in SUBSET acquired[self],
       unoverload \in SUBSET ((acquired[self] \ overload) \intersect overloaded),
       unmute = UNION {mute_map[c] : c \in unoverload}
  do
    overloaded := (overloaded \ unoverload) \union overload;
    
    if gobble[self] \in overloaded then
      with receiver = gobble[self], mute = acquired[self] \ overloaded  do
        available := available \union (acquired[self] \ mute) \union unmute;
        mute_map := (receiver :> mute_map[gobble[self]] \union mute) @@ [m \in unoverload |-> {} ] @@ mute_map;
      end with; 
    else
      available := available \union acquired[self] \union unmute;
      mute_map := [m \in unoverload |-> {} ] @@ mute_map;
    end if;
  end with;
 
  acquired[self] := {}
end process;

end algorithm; *)
\* BEGIN TRANSLATION - the hash of the PCal code: PCal-e47908388deea04c1a66be9ca9c8c984
VARIABLES available, mute_map, required, acquired, gobble, overloaded, pc

(* define statement *)
UnavailableInv == ((UNION Range(mute_map)) \intersect (available \union overloaded)) = {}

OverloadedInv == \A c \in DOMAIN mute_map : mute_map[c] /= {} => c \in overloaded

DisjointMuteMapImageInv == \A c \in Cowns, co \in Cowns: c /= co => mute_map[c] \intersect mute_map[co] = {}


MuteMapProp ==
  []<>(\A k \in DOMAIN mute_map: mute_map[k] = {} \/ k \in overloaded)

VARIABLE cowns

vars == << available, mute_map, required, acquired, gobble, overloaded, pc, 
           cowns >>

ProcSet == (Behaviours)

Init == (* Global variables *)
        /\ available = Cowns
        /\ mute_map = [c \in Cowns |-> {}]
        /\ required = [b \in Behaviours |-> {}]
        /\ acquired = [b \in Behaviours |-> {}]
        /\ gobble = [b \in Behaviours |-> 0]
        /\ overloaded = {}
        (* Process behaviour *)
        /\ cowns \in [Behaviours -> SUBSET Cowns]
        /\ pc = [self \in ProcSet |-> "Create"]

Create(self) == /\ pc[self] = "Create"
                /\ required' = [required EXCEPT ![self] = cowns[self]]
                /\ pc' = [pc EXCEPT ![self] = "Acquire"]
                /\ UNCHANGED << available, mute_map, acquired, gobble, 
                                overloaded, cowns >>

Acquire(self) == /\ pc[self] = "Acquire"
                 /\ IF required[self] /= {}
                       THEN /\ LET next == Min(required[self]) IN
                                 /\ (next \in available) \/ (\E c \in (required[self] \union acquired[self]): c \in overloaded /\ next \in UNION Range(mute_map))
                                 /\ IF (next \in available)
                                       THEN /\ available' = available \ {next}
                                            /\ required' = [required EXCEPT ![self] = required[self] \ {next}]
                                            /\ acquired' = [acquired EXCEPT ![self] = acquired[self] \union {next}]
                                            /\ UNCHANGED mute_map
                                       ELSE /\ Assert((\E c \in (required[self] \union acquired[self]): c \in overloaded /\ next \in UNION Range(mute_map)), 
                                                      "Failure of assertion at line 59, column 9.")
                                            /\ LET c == CHOOSE c \in Cowns: next \in mute_map[c] IN
                                                 /\ mute_map' = [mute_map EXCEPT ![c] = mute_map[c] \ {next}]
                                                 /\ available' = (available \union {next})
                                            /\ UNCHANGED << required, acquired >>
                            /\ pc' = [pc EXCEPT ![self] = "Acquire"]
                       ELSE /\ pc' = [pc EXCEPT ![self] = "Send"]
                            /\ UNCHANGED << available, mute_map, required, 
                                            acquired >>
                 /\ UNCHANGED << gobble, overloaded, cowns >>

Send(self) == /\ pc[self] = "Send"
              /\ \/ /\ TRUE
                    /\ UNCHANGED gobble
                 \/ /\ \E receiver \in Cowns:
                         LET mute == acquired[self] \ overloaded IN
                           IF (receiver \in (overloaded \union UNION Range(mute_map)) \ acquired[self]) /\ (\E b \in Behaviours: receiver \in required[b])
                              THEN /\ gobble' = [gobble EXCEPT ![self] = receiver]
                              ELSE /\ TRUE
                                   /\ UNCHANGED gobble
              /\ pc' = [pc EXCEPT ![self] = "Terminate"]
              /\ UNCHANGED << available, mute_map, required, acquired, 
                              overloaded, cowns >>

Terminate(self) == /\ pc[self] = "Terminate"
                   /\ \E overload \in SUBSET acquired[self]:
                        \E unoverload \in SUBSET ((acquired[self] \ overload) \intersect overloaded):
                          LET unmute == UNION {mute_map[c] : c \in unoverload} IN
                            /\ overloaded' = ((overloaded \ unoverload) \union overload)
                            /\ IF gobble[self] \in overloaded'
                                  THEN /\ LET receiver == gobble[self] IN
                                            LET mute == acquired[self] \ overloaded' IN
                                              /\ available' = (available \union (acquired[self] \ mute) \union unmute)
                                              /\ mute_map' = (receiver :> mute_map[gobble[self]] \union mute) @@ [m \in unoverload |-> {} ] @@ mute_map
                                  ELSE /\ available' = (available \union acquired[self] \union unmute)
                                       /\ mute_map' = [m \in unoverload |-> {} ] @@ mute_map
                   /\ acquired' = [acquired EXCEPT ![self] = {}]
                   /\ pc' = [pc EXCEPT ![self] = "Done"]
                   /\ UNCHANGED << required, gobble, cowns >>

behaviour(self) == Create(self) \/ Acquire(self) \/ Send(self)
                      \/ Terminate(self)

(* Allow infinite stuttering to prevent deadlock on termination. *)
Terminating == /\ \A self \in ProcSet: pc[self] = "Done"
               /\ UNCHANGED vars

Next == (\E self \in Behaviours: behaviour(self))
           \/ Terminating

Spec == /\ Init /\ [][Next]_vars
        /\ \A self \in Behaviours : WF_vars(behaviour(self))

Termination == <>(\A self \in ProcSet: pc[self] = "Done")

\* END TRANSLATION - the hash of the generated TLA code (remove to silence divergence warnings): TLA-b2184c921e6863cb657ebf68e21b9508

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
