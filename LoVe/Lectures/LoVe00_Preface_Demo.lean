import Mathlib.Data.Nat.Prime.Basic
import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.Tactic.Linarith

/-! # LoVe Preface

## Proof Assistants

Proof assistants (also called interactive theorem provers)

* check and help develop formal proofs;
* can be used to prove big theorems, not only logic puzzles;
* can be tedious to use;
* are highly addictive (think video games).

The basic picture:
* You, the programmer, write down some *definitions.*
  These could be data types, functions, mathematical concepts, ...
  Examples: natural numbers, lists, a function that reverses a list.
* Then you write down *specifications* for these definitions.
  A specification is a logical formula -- a "true or false" statement --
  that describes how these definitions behave.
  Example: "If you apply `reverse` to a list twice, you get the original list back"
  (but translated into logic).
* Then you (try to!) write *proofs* of these specifications.
  These proofs are checked by the proof assistant.
  It will report errors, ambiguities, missing steps, ...
  but if it says the proof is correct, it's certainly correct!
  That means your definition must satisfy its specification.

A proof assistant is the combination of the language for writing these things,
the interface for developing proofs, the algorithm for checking these proofs,
and even the logic that defines when a proof is complete.

A selection of proof assistants, classified by logical foundations:

* set theory: Isabelle/ZF, Metamath, Mizar;
* simple type theory: HOL4, HOL Light, Isabelle/HOL;
* **dependent type theory**: Agda, Coq, **Lean**, Matita, PVS, Idris


## Success Stories

Mathematics:

* the four-color theorem (in Coq);
* the odd-order theorem (in Coq);
* the Kepler conjecture (in HOL Light and Isabelle/HOL);
* the Liquid Tensor Experiment (in Lean)

Computer science:

* hardware
* operating systems
* programming language theory
* compilers
* security


## Lean

Lean is a proof assistant developed primarily by Leonardo de Moura
(Amazon Web Services/Lean FRO) since 2012.

Its mathematical library, `mathlib`, is developed by a user community.

We are using Lean 4, a recent version. We use its basic libraries, `mathlib`, and
`LoVelib`. Lean is both a research project and a production language.

Strengths:

* highly expressive logic based on a dependent type theory called the
  **calculus of inductive constructions**;
* extended with classical axioms and quotient types;
* metaprogramming framework;
* modern user interface;
* documentation;
* open source;
* wonderful user community.


## This Course

### Web Site

    https://BrownCS1951x.github.io


### Repository (Demos, Exercises, Homework)

    https://github.com/BrownCS1951x/fpv2024

The file you are currently looking at is a demo.
For each chapter of the Hitchhiker's Guide, there will be approximately
one demo, one exercise sheet, and one homework.

* Lecture demos will be covered in class. These are "lecture notes," in place of slides.
  We'll post skeletons of the demos before class, and completed demos after class.

* Exercises are for weekly lab sessions run by the TAs.

* Homeworks are for you to do on your own, and submit via Gradescope.


### The Hitchhiker's Guide to Logical Verification

    https://cs.brown.edu/courses/cs1951x/static_files/main.pdf

The lecture notes consist of a preface and 14 chapters. They cover the same
material as the corresponding lectures but with more details. Sometimes there
will not be enough time to cover everything in class, so reading the lecture
notes will be necessary.

Download this version, not others that you might find online!


## Our Goal

We want you to

* master fundamental theory and techniques in interactive theorem proving;
* familiarize yourselves with some application areas;
* develop some practical skills you can apply on a larger project (as a hobby,
  for an MSc or PhD, or in industry);
* feel ready to move to another proof assistant and apply what you have learned;
* understand the domain well enough to start reading scientific papers.

This course is neither a pure logical foundations course nor a Lean tutorial.
Lean is our vehicle, not an end in itself.

-/

open Nat

-- here's a proof that there are infinitely many primes, as a mathematical theorem

theorem infinitude_of_primes : ∀ N, ∃ p ≥ N, Nat.Prime p := by
  sorry
  done



-- but really, this is a proof about a *program* called `biggerPrime`!

def biggerPrime (M : ℕ) : ℕ := Nat.minFac (M ! + 1)

#eval biggerPrime 11

theorem biggerPrime_is_prime : ∀ N, Nat.Prime (biggerPrime N) := by
  sorry
  done

theorem biggerPrime_is_bigger : ∀ N, biggerPrime N ≥ N := by
  sorry
  done


-- we can use our verified program to prove our original theorem
theorem infinitude_of_primes2 : ∀ N, ∃ p ≥ N, Nat.Prime p := by
  intro N
  use biggerPrime N
  apply And.intro
  { exact biggerPrime_is_bigger _ }
  { exact biggerPrime_is_prime _ }
  done
