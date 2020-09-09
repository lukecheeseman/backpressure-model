---- MODULE backpressure ----

EXTENDS FiniteSets, Naturals, TLC

Cowns == 1..3
Behaviours == 1..3

Unwrap(s) == CHOOSE x \in s: Cardinality(s) = 1
Range(f) == {f[x]: x \in DOMAIN f}
Min(s) == CHOOSE x \in s: \A y \in s \ {x}: y > x
Intersects(a, b) == a \intersect b /= {}
Subsets(s, min, max) ==
  {cs \in SUBSET s: (Cardinality(cs) >= min) /\ (Cardinality(cs) <= max)}

(* --algorithm backpressure

variables
  \* Cowns available for running behaviours
  available = Cowns,
  \* Cowns that are overloaded
  overloaded = {},
  \* Cowns that are muted
  muted = {},
  \* Cowns that are protected
  protected = {},
  \* Mapping of mutor to muted
  mute_map = [c \in Cowns |-> {}],
  \* Count of behaviours that have yet to run on each cown
  refcount = [c \in Cowns |-> 0],
  \* Count of behaviours with untracked refcounts
  untracked_behaviours = Cardinality(Behaviours),

define
  \* Muted cowns must not be available, overloaded, or protected.
  MutedInv == ~Intersects(muted, UNION {available, overloaded, protected})
  \* All muted cowns must exist in at least one mute map entry.
  MuteMapInv == \A m \in muted: m \in UNION Range(mute_map)
  \* Refcounts must not drop below 0.
  RefcountInv == \A c \in Cowns: refcount[c] >= 0
  \* All refcounts must eventually drop to 0.
  RefcountDropInv ==
    (\A b \in Behaviours: pc[b] = "Done") => (\A c \in Cowns: refcount[c] = 0)

  \* All invalid mute map entries will eventually be removed.
  WillUnmute ==
    []<>(\A k \in DOMAIN mute_map: mute_map[k] = {} \/ k \in overloaded)

  \* Sending to receiver should mute senders.
  TriggersMuting(receiver) == receiver \in (overloaded \union muted)
  \* Cown cannot be muted.
  HasPriority(cown) == cown \in (overloaded \union protected)
end define;

fair process behaviour \in Behaviours
variables
  required \in Subsets(Cowns, 0, 3),
  acquired = {},
begin
Create:
  \* Add a refcount to all required cowns.
  refcount := [c \in required |-> refcount[c] + 1] @@ refcount;
  \* Indicate that the refcounts for this behaviour have been tracked.
  untracked_behaviours := untracked_behaviours - 1;
  \* Empty required set used to represent fewer behaviours in the system.
  if required = {} then goto Done; end if;

RCBarrier:
  \* Wait for refcounts to be valid.
  await untracked_behaviours = 0;

Acquire:
  \* Acquire all cowns, one at a time.
  while required /= acquired do
Protect:
    with remaining = required \ acquired do
      \* Priority (overloaded or protected) receivers protect all other
      \* receivers.
      if \E c \in required: HasPriority(c) then
        \* All previously muted cowns are unmuted when they become protected.
        \* TODO: drop protected state when RC from "priority" cowns is 0
        protected := protected \union remaining;
        available := available \union (remaining \intersect  muted);
        muted := muted \ remaining;
      end if;
    end with;
RunStep:
    with next = Min(required \ acquired) do
      \* Wait for the next required cown to become available.
      await (next \in available)
        \* TODO: see note at bottom of file
        \/ ((next \in muted) /\ (\E c \in required: HasPriority(c)));
      if next \in available then
        \* Acquire the next cown and remove it from the available set.
        acquired := acquired \union {next};
        available := available \ {next};
      end if;
    end with;
  end while;

Action:
  assert \A c \in acquired: refcount[c] > 0;
  assert ~Intersects(acquired, muted);

  \* Any acquired cown may toggle their overloaded state when the behaviour
  \* completes.
  with overload \in SUBSET acquired do
    \* new value of overloaded is used to prevent muting later
    overloaded := (overloaded \ acquired) \union overload;
  end with;

  \* Select zero or one receiver with a nonzero refcount.
  with receiver \in Subsets({c \in Cowns: refcount[c] > 0}, 0, 1) do
    \* Mute senders if the receiver triggers muting and the receiver isn't one
    \* of the senders.
    if (receiver /= {})
      /\ ~Intersects(receiver, acquired)
      /\ TriggersMuting(Unwrap(receiver))
    then
      \* Mute senders that have no priority and are not becoming overloaded.
      with muting = {c \in acquired: ~HasPriority(c)} \ overloaded do
        muted := muted \union muting;
        \* Add muted senders to the mute map entry for the receiver.
        mute_map := [m \in receiver |-> mute_map[m] \union muting] @@ mute_map;
        available := available \union (acquired \ muting);
      end with;
    else
      \* Senders are not muted, so all become available.
      available := available \union acquired;
    end if;
  end with;

  \* Decrement the refcounts of all acquired cowns.
  refcount := [c \in acquired |-> refcount[c] - 1] @@ refcount;
  acquired := {};
end process;

fair+ process scheduler = 0
begin
RCBarrier:
  \* Wait for refcounts to be valid.
  await untracked_behaviours = 0;
MuteMapScan:
  \* Remove invalid mute map entries whenever they may exist.
  while (\E c \in Cowns: refcount[c] > 0) \/ (UNION Range(mute_map) /= {}) do
    with
      \* Invalid keys have a zero refcount or no longer trigger muting.
      keys = {c \in Cowns: (refcount[c] = 0) \/ ~TriggersMuting(c)},
      \* Unmute the muted range of all invalid keys.
      unmuting = muted \intersect (UNION Range([k \in keys |-> mute_map[k]])),
    do
      \* Delete entries and unmute.
      mute_map := [k \in keys |-> {}] @@ mute_map;
      muted := muted \ unmuting;
      available := available \union unmuting;
    end with;
  end while;
end process;

end algorithm; *)

AcquiredUnavailable == \A b \in Behaviours: ~Intersects(acquired[b], available)

====

(* TODO in `RunStep`:

The contition `(next \in muted) /\ (\E c \in required: HasPriority(c))` is used
to ensure that muted cowns never prevent a behaviour scheduled on an overloaded
cown from running indefinitely. Removing this condition from the `await` will
result in the `Termination` property failing. The `Termination` property is used
to check that all behaviours eventually run to completion.

One of the following should be done:
  1. The model should be modified to support `Termination` in a way that can be
     implemented without unacceptable overhead.

  2. The `Termination` property should be replaced by a weaker property, or
     there should be another way to model that muted cowns are eventually
     unmuted.

*)
