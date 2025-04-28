/- --------------------------------------------------------------------------
 -
 -
 -
 -
 -
 -
 -
 -                                       EE 546
 -
 -                               **PROPOSITIONAL LOGIC**
 -
 -                   DEPARTMENT OF ELECTRICAL AND COMPUTER ENGINEERING
 -                              UNIVERISITY OF WASHINGTON
 -                                 PROF.  ERIC KLAVINS
 -
 -                                     WINTER 2025
 -
 -
 -
 -
 -
 -
 -
 -
 -
 -
 ------/

/- # PROPOSITIONS

A `proposition` is a statement that is either true or false. The following are examples:

  - It is raining outside.
  - All cats are animals.
  - Darth Vader is Luke's Father.
  - Four is greater than five.

In propositional logic, we assign `propositional variables` to represent the value of these statments. So we might make the assignments:

  p := It is raining outside.
  q := All cats are animals.
  r := Darth Vader is Luke's Father.
  s := Four is greater than five.

Note that we are not saying p is the English language sentence "It is raining outside". We are not doing natural language processing here. Rather, we are saying that p is a `propositional variable` that is true when it actually is raining outside, and false otherwise. To determine the truth value of p, we would need some way to check whether it is raining outside (as well as some specifics like outside _where_ and _when_? For now, we'll just be informal about such things). -/











/- # ATOMIC VS COMPOUND PROPOSITIONS

A propsition that corresponds to a direct measurement or other basic truth is called `atomic`. It cannot be sub-divided into more basic propositions. Otherwise it is called compound. For example, the proposition

  - It is raining outside or all cats are animals.

is a compound proposition that uses the _connective_ "or" to connect two atomic propositions. Symbolically, we write

  p ∨ q

for "p or q".

Students used to digital logic will wonder why we are using ∨ instead of the symbol +. The main reason is that + will usually mean actual addition when things get more complicated. Thus, mathematicans have invented new symbols for logical connectives. Here are the most important for our current purposes:

  ¬p               not p
  p ∨ q            p or q
  p ∧ q            p and q
  p → q            p implies q
  p ↔ q            p if and only if q

-/






/- # NOT AND IF AND ONLY IF

We also have the propositional ⊥ which denotes `absurdity`. In intuitionistic logic, ¬p is just shorthand for

  p → ⊥

In Lean, ⊥ is denoted by False:

-/

#check False

/-

Also note that ↔ is just shorthand for → in both directions:

  p ↔ q  ≡  p → q ∧ q → p

-/












/- # THE INDUCTIVE DEFINITION OF PROPOSITIONS

Formally, we define the syntax of propositional logic without these two connectives. Let

  V = { p, q, r, s, ... }

be a set of propositional variables. Then the set of propositions Φ is defined inductively by the follow rules:

  ⊥ is a proposition
  p is a proposition for all p ∈ V
  Φ₁ ∨ Φ₂, Φ₁ ∧ Φ₂ and Φ₁ → Φ₂ are propositions whenever Φ₁ and Φ₂ are propositions.

-/














/- # CONSTRUCTIVE PROOFS

The goal is this chapter is to define a mathematical framework in which we prove statements by constructing proofs. In particular,

  - To prove p ∧ q we construct a proof of p and another proof of q.
  - To prove p ∨ q we construct a proof of p or we construct a proof of q.
  - To prove p → q we supply a method for converting a proof of p into a proof of q
  - To prove ¬p (which is p → ⊥) we supply a method to convert a proof of p to ⊥

-/

















/- # EXAMPLE CONSTRUCTIVE PROOF IN LEAN -/

example (p q r : Prop) : p ∧ (q ∨ r) ↔ (p ∧ q) ∨ (p ∧ r) :=
  Iff.intro
    (λ h : p ∧ (q ∨ r) =>
      have hp : p := h.left
      have hqr : q ∨ r := h.right
      Or.elim hqr
        (λ hq : q => Or.inl (And.intro hp hq))
        (λ hr : r => Or.inr (And.intro hp hr))
    )
    (λ h : (p ∧ q) ∨ (p ∧ r) =>
      Or.elim h
        (λ hpq : p ∧ q => And.intro hpq.left (Or.inl hpq.right))
        (λ hpr : p ∧ r => And.intro hpr.left (Or.inr hpr.right))
    )

/- By the end of next week, this will be easy to understand! -/










/- # COMPARISON TO CLASSICAL LOGIC

We have defined `intuitionistic` logic or `constructive logic`, different from `classical logic`. In classical logic, the truth of a statement like

  p ∨ ¬p

is guaranteed by the `law of the exluded middle`. You know one of them must be true. In constructive mathematics, you have to either construct a proof of p or construct a proof of ¬p. As an example, consider the proposition:

  The universe is infinite or the universe is finite.

Neither part of this compound proposition currently has a proof. Classically, we would still conclude it is true, but constructively we are just stuck. Similar issues arise with famous mathematical conjectures such as

  P = NP or P ≠ NP

and

  There are either a finite number of twin primes, or an infinite number of twin primes.

These statements may be proved some day, but for now, we cannot conclude they are true using constructive mathematics. -/







/- # DOUBLE NEGATION

Similar to the law of the excluded middle is double negation:

  ¬¬p ↔ p

Classically, this is a tautology (a proposition that is always true). But constructively, from a proof of "it is not the case that p is not true" one cannot necessarily construct a proof that p is true.

As a result, `proof by contradiction` is not valid constructively, because in proof by contradition one follows the procedure:

  To prove p, assume ¬p and derive ⊥.

Just because we have a way to transform a proof of ¬p into ⊥ does not mean we can have a construction of a proof of p. -/













/- # CONTEXTS

We now begin to build a framework for proving theorems in propositional logic. The first thing we need is a way to keep track of what propositions we currently know in the course of proving something.

To this end we define a `context` to be a finite set of propositions. Given two contexts Γ and Δ we can take their union Γ ∪ Δ to make a new context. The notation is a bit cumbersome, so we write Γ,Δ instead. In particular, if φ ∈ Φ then Γ,φ is shorthand for Γ ∪ {φ}.

If we can show that a proposition φ is true whenever all the propositions in a context Γ are true, we write

  Γ ⊢ φ

which reads gamma `entails` φ. Furthermore, if a proposition φ is tautology (meaning it is always true like p ↔ p) then it is true independent of any context. That is, the empty context entials any tautology. Thus, we write

  ⊢ φ

to mean ∅ ⊢ φ. We will define precisely what the entails relationship means next.

Note: Scroll back to the Lean proof above and look at the context in the InfoView. -/







/- # RULES OF INFERENCE

A `rule of inference` is set of `premises` and a `conclusion` that can be drawn from those premises. The propositional logic we define has only a handful of rules of inference from which all proofs can be constructed. They are presented with a name followed by what looks like a fraction with the premises listed on top and the conslusion on the bottom.

                Γ₁ ⊢ A    Γ₂ ⊢ B    Γ₃ ⊢ C
  `RULE NAME`  ————————————————————————————
                          Γ ⊢ D

In this schemantic, the rule has three premises, each of which describe an assumption that a particular context entails a particular proposition. And the rule has one conclusion, stating the entailment you are allowed to conclude. Usually, the contexts listed and the propositions are related in some way. -/














/- # AXIOMS

The first rule has no premises and simply states that φ can be concluded from any context containing φ. Said constructively, if we have a proof of φ, then obviously we can construct a proof of φ.

  `AX`  ——————————
         Γ,φ ⊢ φ

-/


















/- # AND RULES

Next we have three rules for the ∧ connective:

              Γ ⊢ φ   Γ ⊢ ψ
  `∧-Intro` ———————————————————
               Γ ⊢ φ ∧ ψ

                  Γ ⊢ φ ∧ ψ
  `∧-Elim-Left` ——————————————
                    Γ ⊢ φ

                  Γ ⊢ φ ∧ ψ
  `∧-Elim-Right` —————————————
                    Γ ⊢ ψ

Whenever we see "Intro" that means we are introducing a connective (in this case ∧) into our conclusion. Whenever we see "Elim" that means we are eliminating part of a compound statement in our conclusion. Here, the `And Introduction` rule shows that we can construct a proof of φ ∧ ψ whenever the context contains a proof of φ and a proof of ψ. The `And Elimination` rules allow us to "eliminate" half of the proposition φ ∧ ψ to conclude the weaker statement φ or to conclude the weaker statement ψ. Said differently, if we have a proof of φ∧ψ then we can construct a proof of φ by just eliminating the part of the proof of φ∧ψ that shows ψ.

Note: These rules are usually read bottom up. -/





/- # OR RULES

Then we have three rules for the ∨ connective:
                   Γ ⊢ φ
 `∨-Intro-Left` ———————————
                 Γ ⊢ φ ∨ ψ

                    Γ ⊢ ψ
 `∨-Intro-Right` ————————————
                  Γ ⊢ φ ∨ ψ

            Γ,φ ⊢ ρ    Γ,ψ ⊢ ρ    Γ ⊢ φ ∨ ψ
 `∨-Elim` ————————————————————————————————————
                      Γ ⊢ ρ

The OR Introduction rules allow us to conclude φ ∨ ψ from one of its parts. The OR elimination rule looks complicated, but it is straightforward. It says that if we know Γ ⊢ φ ∨ ψ then we know that Γ must entail either φ or ψ. If we also know that both φ and ψ separately entail ρ, then we know that Γ must entail ρ. -/








/- # IMPLIES RULES

Next we have two rules for the → connective:

              Γ,φ ⊢ ψ
  `→-Intro` ————————————
             Γ ⊢ φ → ψ

            Γ ⊢ φ → ψ    Γ ⊢ φ
  `→-Elim` —————————————————————
                 Γ ⊢ ψ

The IMPLIES Introduction rule allows us to introduce φ → ψ whenever we have Γ and φ together entailing ψ. The IMPLIES Elimination rule is also know as `Modus Ponens`. It states that if we know φ implies ψ and we know φ, then we know ψ.

(Looking ahead, notice that implies is written with an arrow → just like function abstraction in the λ-calculus. This is because one way to think about a proof of φ→ψ is to require it to have the form of a function that converts proofs of φ into proofs of ψ.) -/











/- # EX FALSO

Finally, we have the a rule for the ¬ connective:

              Γ ⊢ ⊥
  `⊥-Elim` ————————————
              Γ ⊢ φ

which states that you can conclude anything if you have a proof of ⊥. This rule is also know as `ex falso sequitur quodlibet` or just `ex falso` or the `principle of explosion`!

-/

















/- # PROOFS

A `proof` that Γ ⊢ φ is sequence of statements of the form Γ' ⊢ φ' each of which is either (a) an axiom or (b) obtained from previous statements in the sequence by one of the inference rules. -/
























/- # EXAMPLE 1

As an example, we will prove the statement

  ∅ ⊢ (p∧q)→p

Working backwards from this goal, we see that →-Intro can be applied to produce this statement where φ is p∧q and ψ is p. Thus, we get an instance of →-Intro of the form

    p∧q ⊢ p
  ———————————          (Instantiation of →-Intro)
   ⊢ (p∧q)→p

We have now a simpler problem, which is to show p∧q ⊢ p. The ∧-Elim-Left rule applies here with φ=p∧q, ψ=p, and Γ={p∧q} giving us the instance

    p∧q ⊢ p∧q
  ——————————————       (Instantiation of ∧-Elim-Left)
     p∧q ⊢ p

-/








/- # EXAMPLE 1 PROOF PRESENATION

And now we have an even simpler problem, which is to show that p∧q ⊢ p∧q. But this matches the axiom rule with Γ={p∧q} and φ = p∧q. Putting all this together into a proof gives us the following:

  1) p∧q ⊢ p∧q          axiomatically
  2) p∧q ⊢ p            from (1) via ∧-Elim-Left
  3) ⊢ (p∧q)→p          from (2) via →-Intro

And that's it. Our first proof!

What you should take away from this is constructing this proof is a purely syntactic endeavor. One can easily imagine an algorithm that does this automatically by pattern matching a given sub-goal against the Γ, φ and ψ in the description of a inference rule. The challenge is, of course, as we introduce more expressibility into our logic, and more inference rules, finding the right rules to apply at the right time amounts to a brute force search of all possible inference rules and all possible ways of instantiating those inference rools.

The other thing to notice is that the proof itself looks a lot like a program. In Lean and similar construction-based theorem provers, this observation is made precise. And it will turn out that writing proofs and writing programs amount to the same thing! -/






/- # EXAMPLE 2

Here is a slightly more complicated example. Let's prove

  ⊢ ¬p→(p→q)

Recall ¬p is just shorthand for p→⊥. So we're actually trying to prove

  ⊢ (p→⊥)→(p→q)

Once again, working backwards, we can apply →-Intro to get

  p→⊥ ⊢ p→q

and then apply →-Intro again to get

  p→⊥,p ⊢ q

Our context now contains both ¬p and p. Using ⊥-elim we get

  p→⊥,p ⊢ ⊥

This subgoal matches the form of →-Elim with φ=p and ψ=⊥. Using this rule, we get two further subgoals that are just axioms:

  p→⊥,p ⊢ p→⊥      and      p→⊥,p ⊢ p

-/

/- # PROOF 2 PRESENTATION

Putting this all together, we get the following proof:

  1) p→⊥,p ⊢ p→⊥        axiomatically
  2) p→⊥,p ⊢ p          axiomatically
  3) p→⊥,p ⊢ ⊥          from (1) and (2) via →-Elim
  4) p→⊥,p ⊢ q          from (3) via ⊥-elim
  5) p→⊥ ⊢ p→q          from (4) via →-Intro
  6) ⊢ (p→⊥)→(p→q)      from (5) via →-Intro

And we're done! This is complicated though. Clearly we need a proof assistant to help us! We'll show how we can use the Simply Typed Lambda Calculus to do these proofs in Lean soon.

-/












/- # IN CLASS EXERCISES

- Prove ∅ ⊢ p → (p ∨ q)
- Prove ∅ ⊢ (p ∨ q) → (q ∨ p)

-/












/- # THE LAW OF THE EXCLUDED MIDDLE

As we said, the law of the excluded middle states that

  ⊢ φ ∨ ¬φ

for all propositions φ. However, this statement is not provable using the inference rules above. To prove this meta-mathematical observation is beyond the scope of this lecture and requires an argument about the formal `semantics` of intuitionist propositional logic. For now, accept the fact that φ ∨ ¬φ cannot be proved rom the inference rules given, despite its seeming obviousness.

For this reason, intutionistic logic is weaker than classical logic. However, we can obtain classical logic by adding the above as a new axiom. When we get to proving statements in Lean, we'll see that we can add this axiom into our proofs if we would like to, so it is not big problem. However, it is also remarkable how much of mathematics we can prove without this axiom.

-/









/- # REFERENCES

Morten Heine Sørensen, Pawel Urzyczyn
"Lectures on the Curry-Howard Isomorphism"
Elsevier. 1st Edition, Volume 149 - July 4, 2006.
  - Chapter 2 describes Intuitionistic Propositional Logic

-/
