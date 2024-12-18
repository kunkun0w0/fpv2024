import LoVe.LoVelib

/- # Final Project: Deterministic Finite Automaton Minimization

# Author: Zekun Li  -/

/- Abstract:
This work uses Lean4 to define and make proofs on Deterministic Finite
Automaton Minimization, including partitioning states and removing
unreachable states.
-/

namespace LoVe


/- ## 1. Deterministic Finite Automaton (DFA)

## Introduction
In the theory of computation, deterministic finite automaton (DFA) is a
finite-state machine that accepts or rejects a given string of symbols,
by running through a state sequence uniquely determined by the string.
Deterministic refers to the uniqueness of the computation run.

A DFA is defined as an abstract mathematical concept, but is often
implemented in hardware and software for solving various specific problems
such as lexical analysis and pattern matching. For example, a DFA can model
software that decides whether or not online user input such as email
addresses are syntactically valid.

## Formal Definition
A deterministic finite automaton M is a 5-tuple, (Q, Σ, δ, q₀, F),
consisting of:
- a finite set of states Q
- a finite set of input symbols called the alphabet Σ
- a transition function δ : Q × Σ → Q
- an initial or start state q₀ ∈ Q
- a set of accept states F ⊆ Q

Let w = a₁a₂...aₙ be a string over the alphabet Σ. The automaton M accepts
the string w if a sequence of states, r₀, r₁, ..., rₙ, exists in Q with the
following conditions:
- r₀ = q₀
- rᵢ₊₁ = δ(rᵢ, aᵢ₊₁), for i = 0, ..., n − 1
- rₙ ∈ F

In words, the first condition says that the machine starts in the start
state q0. The second condition says that given each character of string w,
the machine will transition from state to state according to the transition
function δ. The last condition says that the machine accepts w if the last
input of w causes the machine to halt in one of the accepting states.
Otherwise, it is said that the automaton rejects the string. The set of
strings that M accepts is the language recognized by M and this language is
denoted by L(M).
-/


/- Let's first define the structure of DFA
-/

structure DFA (State Alphabet : Type) where
  states : List State
  alphabet : List Alphabet
  transition : State → Alphabet → Option State
  start_state : State
  accept_states : List State

/- The we define the procedure of transistion execution.
-/

def DFA.run {State Alphabet : Type}
  (dfa : DFA State Alphabet)
  (input : List Alphabet) : Option State :=
  let rec step (current_state : State) (remaining_input : List Alphabet) : Option State :=
    match remaining_input with
    | [] => some current_state
    | x :: xs =>
      match dfa.transition current_state x with
      | none => none
      | some next_state => step next_state xs
  step dfa.start_state input

/- So, we can design a function to validate the input string
-/

def DFA.accepts {State Alphabet : Type} [BEq State]
  (dfa : DFA State Alphabet)
  (input : List Alphabet) : Bool :=
  match DFA.run dfa input with
  | none => false
  | some final_state => dfa.accept_states.contains final_state

/- Here is a simple check!
-/

def exampleDFA : DFA ℕ Char :=
  { states := [0, 1, 2],
    alphabet := ['a', 'b'],
    transition := fun s a =>
      match s, a with
      | 0, 'a' => some 1
      | 1, 'b' => some 2
      | _, _   => none,
    start_state := 0,
    accept_states := [2] }

def testInput1 := ['a', 'b']
def testInput2 := ['a', 'a']

#eval exampleDFA.accepts testInput1  -- should be true
#eval exampleDFA.accepts testInput2  -- should be false


/- **Extend Transition Function for DFA**
-/

/- An extended transition function δ' traces the path of an automaton
and determines the final state when an initial state q and an input string
w = a₁a₂...aₙ are passed through it.

The difference between a simple transition function and the extended
transition function is that the former performs a transition of a single
character/instance. In contrast, the latter performs the transitions on a
complete string.

For example, here is the transition table of a simple DFA:
|              |     a      |     b      |
|--------------|------------|------------|
|  ->q0        |    q1      |     q0     |
|    q1        |    q1      |     q2     |
|   *q2        |    q1      |     q0     |

Let's take an input string "abab". Its extended transition
function will be as follows:

δ'(q0, "abab")

We remove the rightmost characters one by one using the
recursion rule:

δ'(q0, "abab") = δ(δ'(q0, "aba"), "b")
               = δ(δ(δ'(q0, "ab"), "a"), "b")
               = δ(δ(δ(δ'(q0, "a"), "b"), "a"), "b")
               = δ(δ(δ(δ(δ'(q0, ε), "a"), b), "a"), "b")
               = δ(δ(δ(δ(q0, "a"), b), "a"), "b")
               = q2

where ε is the empty string.

The mathmatical definition of the extended transition function is as
follows: δ' : Q × Σ' → Q

Based on the definition of the extended transition function, the lean4 code
is as follows:
-/

def DFA.run_ext {State Alphabet : Type}
  (dfa : DFA State Alphabet)
  (q : State)
  (input : List Alphabet) : Option State :=
  let rec step (current_state : State) (remaining_input : List Alphabet) : Option State :=
    match remaining_input with
    | [] => some current_state
    | x :: xs =>
      match dfa.transition current_state x with
      | none => none
      | some next_state => step next_state xs
  step q input

/- Different from DFA.run, DFA.run_ext can specifiy the starting state of
transition procedure as any state, not only q0.
-/

/- ## 2.States Partitioning
Let's first learn how to partition a list of numbers into subsets based on
some criteria.

Here is two examples about partitioning a list of Nat numbers based on:
1. odd and even numbers
2. the remainder of division by a number n
-/

def partition_odds_and_evens (l : List Nat) : List (List Nat) :=
  let (odds, evens) := l.partition (fun x => x % 2 = 1)
  odds :: evens :: []

#eval partition_odds_and_evens [1, 2, 3, 4, 5, 6]

def group_by_mod (l : List Nat) (n : Nat) : List (List Nat) :=
  l.groupBy (fun x y => x % n = y % n)

#eval group_by_mod [1, 2, 3, 4, 5, 6] 2

/- After learning the basic operation about partitioning, let's partition
the states of a DFA into two subsets: accept states and non-accept states.
-/
def BigDFA : DFA Char ℕ :=
  { states := ['a', 'b', 'c', 'd', 'e', 'f'],
    alphabet := [0, 1],
    transition := fun s a =>
      match s, a with
      | 'a', 0 => some 'b'
      | 'b', 0 => some 'a'
      | 'a', 1 => some 'c'
      | 'b', 1 => some 'd'
      | 'c', 0 => some 'e'
      | 'd', 0 => some 'e'
      | 'c', 1 => some 'f'
      | 'd', 1 => some 'f'
      | 'e', 0 => some 'e'
      | 'e', 1 => some 'f'
      | 'f', 0 => some 'f'
      | 'f', 1 => some 'f'
      | _, _   => none,
    start_state := 'a',
    accept_states := ['c', 'd', 'e'] }


def initial_partition {State : Type} [BEq State]
  (states : List State)
  (accept_states : List State) : List (List State) :=
  let non_accepting := states.filter (fun s => ¬ accept_states.any (fun a => a == s))
  non_accepting :: accept_states :: []

#eval initial_partition BigDFA.states BigDFA.accept_states
-- should be [['a', 'b', 'f'], ['c', 'd', 'e']]

/-To get more fine-grained division, we can group the states by equivalence.
The definition of equivalence is as follows:
Two states q1 and q2 are equivalent if for any input string w, starting from
either state leads to the same acceptance or rejection outcome.
Based on this criteria, we propose the division procedure as follows:
1. First partition the states into two subsets: accept states (T) and
   non-accept states (N), i.e., P₀ = {T, N}. The elements in P are called
   *Equivalence Class*, which means the states in the same class are
   equivalent.
2. Given a partition Pₖ, for each action a in the alphabet Σ:
   - For each equivalence class C in Pₖ:
     - We calculate the next state s' for each state s ∈ C when taking
       action a, i.e., s' = δ(s, a).
     - We partition the states in C into groups based on whether the next
       state s' is in the same equivalence class in Pₖ and update the Pₖ.
   - Get the new partition Pₖ₊₁.
3. Repeat step 2 until the partition Pₖ and Pₖ₊₁ are the same.
-/

/-We first implement refine a class by a single action
-/

def refine_class {State Alphabet : Type} [BEq State]
  (transition : State → Alphabet → Option State)
  (partition : List (List State))
  (a : Alphabet)
  (eq_class : List State) : List (List State) :=
  let next_states := eq_class.map (fun s => transition s a)
  let trans_pairs := eq_class.zip next_states
  let trans_pairs' : List (State × State) :=
    trans_pairs.map (fun (s, s') => (s, match s' with
                                        | some s' => s'
                                        | none => s))
  let next_states' : List State := trans_pairs'.map (fun (s, s') => s')
  let target_states_class_idx := next_states'.map (fun s => partition.findIdx (fun c => c.contains s))
  let paired := eq_class.zip target_states_class_idx
  let grouped := paired.groupBy (fun (_, k1) (_, k2) => k1 == k2)
  let refined := grouped.map (fun pairs => pairs.map (fun (s, _) => s))
  refined

#eval refine_class BigDFA.transition (initial_partition BigDFA.states BigDFA.accept_states) 0 ['a', 'b', 'f']
-- should be [['a', 'b', 'f']]
#eval refine_class BigDFA.transition (initial_partition BigDFA.states BigDFA.accept_states) 1 ['a', 'b', 'f']
-- should be [['a', 'b'], ['f']]

/- Then we implement the whole partition refinement step.
We only conduct one loop of alphabet.
-/

def refine_partition {State Alphabet : Type} [BEq State]
  (transition : State → Alphabet → Option State)
  (partition : List (List State))
  (alphabet : List Alphabet) : List (List State) :=
  partition.bind (fun eq_class =>
    alphabet.foldl (fun acc a =>
      acc.bind (fun sub_class => refine_class transition partition a sub_class)
    ) [eq_class])

#eval refine_partition BigDFA.transition (initial_partition BigDFA.states BigDFA.accept_states) BigDFA.alphabet

/- At last, we can implement the whole partition refinement loop.
Note that the refinement loop contains a maximum number of iterations and
it must not greater than |Σ|×|Q|.
-/

def EqClassPartitionDFA {State Alphabet : Type} [BEq State]
  (transition : State → Alphabet → Option State)
  (alphabet : List Alphabet)
  (initial_partition : List (List State))
  (max_iterations : Nat) : List (List State) :=
  if max_iterations = 0 then
    initial_partition
  else
    let current_partition := refine_partition transition initial_partition alphabet
    if current_partition == initial_partition then
      current_partition
    else
      EqClassPartitionDFA transition alphabet current_partition (max_iterations - 1)

#eval EqClassPartitionDFA BigDFA.transition BigDFA.alphabet (initial_partition BigDFA.states BigDFA.accept_states) (BigDFA.states.length * BigDFA.alphabet.length)

/- ## 3.DFA Minimization
In the previous section, we implemented the partition refinement step
for DFA based on equivalence. And we reduce the amount of states in a DFA
while presevering the behavior towards any valid input string!

To minimize the DFA, we also need to remove the unreachable states.
-/

/- The most easiest way to remove unreachable states is to traverse the DFA
from the start state by repeating the alphabet.
1. Start from the start state s₀, then create the initial reachable states
   list R=[s₀].
2. For each state s in R, calculate the next state s' for each action a in
   the alphabet Σ, i.e., s' = δ(s, a). Then merge the new states into R.
3. Repeat step 2 until R is not changed.

Similar to the partition refinement step, the maximum number of iterations
must not greater than |Q|×|Σ|.
-/


def BigDFA_2 : DFA Char ℕ :=
  { states := ['a', 'b', 'c', 'd', 'e', 'f', 'g'],
    alphabet := [0, 1, 2],
    transition := fun s a =>
      match s, a with
      | 'a', 0 => some 'b'
      | 'b', 0 => some 'a'
      | 'a', 1 => some 'c'
      | 'b', 1 => some 'd'
      | 'c', 0 => some 'e'
      | 'd', 0 => some 'e'
      | 'c', 1 => some 'f'
      | 'd', 1 => some 'f'
      | 'e', 0 => some 'e'
      | 'e', 1 => some 'f'
      | 'f', 0 => some 'f'
      | 'f', 1 => some 'f'
      | 'g', 2 => some 'g'
      | _, _   => none,
    start_state := 'a',
    accept_states := ['c', 'd', 'e'] }

#eval BigDFA_2.transition 'a' 2
/- First, we define some help function to help us remove the duplicates in
a list.
-/
def removeDuplicates {a : Type} [BEq a] (lst : List a) : List a :=
  let rec aux (seen : List a) (remaining : List a) : List a :=
    match remaining with
    | []      => seen.reverse
    | x :: xs =>
      if seen.contains x then
        aux seen xs
      else
        aux (x :: seen) xs
  aux [] lst

#eval removeDuplicates [1, 2, 3, 1, 2, 4, 5, 6, 3]
#eval removeDuplicates ['a', 'b', 'c', 'a', 'b', 'd', 'e', 'f', 'c']

/- The we get the reachable states in the DFA.
-/
def reachable_states {State Alphabet : Type} [BEq State]
  (transition : State → Alphabet → Option State)
  (current_set : List State)
  (alphabet : List Alphabet)
  (max_iterations : Nat) : List State :=
  if max_iterations = 0 then
    current_set
  else
    let new_states := removeDuplicates (current_set.bind (fun s =>
      alphabet.map (fun a => match transition s a with
                             | some s' => s'
                             | none => s)))
    let merged_states := removeDuplicates (current_set ++ new_states)
    reachable_states transition merged_states alphabet (max_iterations - 1)

#eval BigDFA_2.states -- ['a', 'b', 'c', 'd', 'e', 'f', 'g']
#eval reachable_states BigDFA_2.transition [BigDFA_2.start_state] BigDFA_2.alphabet (BigDFA_2.states.length * BigDFA_2.alphabet.length)
-- ['a', 'b', 'c', 'd', 'e', 'f']

def remove_unreachable_states {State Alphabet : Type} [BEq State]
  (dfa : DFA State Alphabet) : DFA State Alphabet :=
  let reachable := reachable_states dfa.transition [dfa.start_state] dfa.alphabet (dfa.states.length * dfa.alphabet.length)
  let has_transition : Alphabet → Bool := fun a =>
    let next_states := reachable.map (fun s => dfa.transition s a)
    next_states.any (fun s' => s'.isSome)

  {
    states := reachable
    alphabet := dfa.alphabet.filter (fun a => has_transition a)
    transition := dfa.transition
    start_state := dfa.start_state
    accept_states := dfa.accept_states.filter (fun s => reachable.contains s)
  }

instance {State Alphabet : Type} [ToString State] [ToString Alphabet] : Repr (DFA State Alphabet) where
  reprPrec dfa _ :=
    let transitions : List String :=
      dfa.states.bind (fun s =>
        dfa.alphabet.map (fun a =>
          match dfa.transition s a with
          | some target => toString s ++ " -- " ++ toString a ++ " --> " ++ toString target
          | none => toString s ++ " -- " ++ toString a ++ " --> [INVALID]"))
    "DFA:\n" ++
    "States: " ++ toString dfa.states ++ "\n" ++
    "Alphabet: " ++ toString dfa.alphabet ++ "\n" ++
    "Start State: " ++ toString dfa.start_state ++ "\n" ++
    "Accept States: " ++ toString dfa.accept_states ++ "\n" ++
    "Transitions:\n" ++ transitions.foldl (fun acc t => acc ++ t ++ "\n") ""

#eval BigDFA_2
#eval remove_unreachable_states BigDFA_2

/- Based on the above functions, we can implement the DFA minimization.
-/

def getFirst {α : Type} [Inhabited α] (lst : List α) : α :=
  match lst with
  | [] => panic! "Empty list!"
  | x :: _ => x

def DFA.minimize {State Alphabet : Type} [BEq State] [Inhabited State]
  (dfa : DFA State Alphabet) : DFA (List State) Alphabet :=
  let reachable := reachable_states dfa.transition [dfa.start_state] dfa.alphabet (dfa.states.length * dfa.alphabet.length)
  let new_dfa := remove_unreachable_states dfa
  let init_partition := initial_partition new_dfa.states new_dfa.accept_states
  let final_partition := EqClassPartitionDFA new_dfa.transition new_dfa.alphabet init_partition (new_dfa.states.length * new_dfa.alphabet.length)
  -- create the DFA with the minimized states
  let new_states := final_partition
  let new_start_state := (final_partition.find?
    (fun eq_class => eq_class.contains new_dfa.start_state )).get!
  let new_accept_states := final_partition.filter (fun eq_class =>
    eq_class.any (fun state => new_dfa.accept_states.contains state))
  let new_transition : List State → Alphabet → Option (List State) :=
    fun eq_class a =>
      let rep_state := getFirst eq_class
      let target := new_dfa.transition rep_state a
      match new_dfa.transition rep_state a with
      | none => none
      | some target => final_partition.find? (fun eq_class => eq_class.contains target)
  {
    states := new_states,
    alphabet := new_dfa.alphabet,
    transition := new_transition,
    start_state := new_start_state,
    accept_states := new_accept_states
  }

#eval BigDFA_2
#eval BigDFA_2.minimize


end LoVe
