/- # The Simply Typed λ-Lambda Calculus

## Background

The **λ-calculus** was introduced in the 1930s by Alonzo Church as a way to represent how functions on natural numbers are calculated using symbols. The goal was to determine whether every function on the natural numbers had an effective means of being calculated.

Said differently, the question is: Does every function have an algorithm? Astonishingly, Church showed that the answer is "no". In fact, there are functions on the natural numbers for which there is no effective algorithm. Church's 1935 paper "An unsolvable problem in elementary number theory" proved this result.

The reasoning, roughly, is this:

  - Devise a simple programming language, the λ-calculus
  - Define computation as rewriting operations on λ-calculus terms
  - Correspond to every term a natural number
  - Conclude that questions about terms are thus questions about numbers
  - Show there are more functions from terms into terms than there are terms.

A specific problem that Church showed to be unsolvable is: Given λ-calculus terms M and N, show there does not exist a λ-calculus function that can determine whether M can be rewritten as N. Those who have studied theoretical computer science, may be familiar with Alan Turing's similar result which shows there is no Turing Machine that can determine whether a given Turing Machine eventually terminates. In fact, the λ-calculus can simulate Turing Machines and vice verse.

The Church-Turing Thesis is the observation that _all_ formalizations of computation are in fact equivalent to the λ-calculus or, equivalently, Turing Machines. The former is more convenient for symbolic reasoning, while the latter is more akin to how electromechanical computers actually work.

## Programming Languages

Thus, the λ-calclus and the formal notion of computation has its roots in the foundations of mathematics. Later, around the 1960s, linguists and computer scientists realized that the λ-calculus was an useful framework for the theory and design of programming languages.

Simultaenously, logicians were becoming frustrated with Set Theory as a foundation for mathematics and started exploring Type Theory as an alternative. Around the 1990s many of these ideas came together, especially through the work of Thierry Coquand on the Calculus of Constructions. It was observed that typed programming languages were not only an ideal foundation for all of mathematics, they could be used to develop computational proof assistants and theoerm provers.

## Curry's Paradox

The original formulation of the λ-calculus allowed for infinite loops, as do most programming languages. This made the λ-calculus expressive enough for Church to prove his undecidability results, but it caused other problems when logicians wished to use formalisms like the λ-calculus as systems of logic.

Haskel Curry discovered that one could encode the following paradox:

  - Consider the self-referential statement X = X → Y where Y is _any_ statement.
  - Certainly X → X is true for any statement X.
  - Substituting X → Y for the second X gives X → (X → Y)
  - This statement is equivalent to X → Y, which is the same as X
  - Thus X is true
  - So Y is true since X → Y

For example, X → Y could mean "If this sentence is true, then 1 > 0." Any framework in which you can make this argument allows you to prove any statement Y, and so the framework is useless logically.

## Types

The solution was to give _types_ to all terms in the λ-calculus. We will see below that certain self referential programs are impossible to assign types to. At the same time, infinite loops are no longer allowed, making the formalism not as powerful from a computational point of view.

Thus was born the _simply-typed λ-calculus_. Eventually, more complicated types were added, in which type definitions could depend on other types or on even terms. Most modern programming languages and some logical frameworks have these properties.

Church's paper on the subject is quite complicated, elucidating ideas that were fairly novel at the time. Since then, comptuer scientists have refined the ideas into a very simple framework, which is presented here, and which can be found in numerous textbooks. The notes in the first part of this section follow video lectures by students of Prof. Uwe Nestmann at the Technical University of Berlin, except that I have restated the formulas in Lean. A link to the videos can be found in the references at the end of this chapter. A Google search will yield hundreds of similar lectures, notes, books, and papers.

### Basic Types

The `simply typed λ-calculus` is an extremely simple programming language that nevertheless captures the essence of computation. It uses type expressions and terms that have those types. We start with the types. First, we assume a base type. In Lean the base type is called `Type`. You can ask lean what `Type` is using the `#check` directive (which stands for "Type Check"). -/

#check Type

/- Lean tells you `Type` has `Type 1`, which is a synonym for `Type`. Don't worry about this right now and just accept that `Type` is a type. One constructs new types using the arrow `→` as in the following examples: -/

#check Type → Type
#check Type → (Type → Type)
#check (Type → Type) → Type

/- That is, whenevever τ is a type, so is τ → τ. Arrow types are supposed to denote function types. So τ → τ is the type of any function that takes objects in τ and returns objects in τ. Note that the arrow → associates to the right. So the second expression above is equivalent to `Type → Type → Type`.

### Type Variables and Applications

You can also define type variables using `def` -/

def A := Type
def B := Type → Type

/- Which looks a bit more like what you would see in a textbook on type theory. Now you can construct more types. -/

#check A → B


/- ## Terms

Next, we define the terms of the lambda calculus. These are the programs. We start with **variables**, for example `x` and `f`, which we declare in Lean as follows: -/

variable (x : A)               -- declare a variable x of type a
variable (f : A → A)           -- declare a function f from A into A

#check x
#check f

/- What we've said here is that `x` is a simple object with type `A`, while `f` is an function type from `A` into `A`. Next we have **applications**. These have the form `e₁ e₁` where `e₁` and `e₂` are terms. For example, -/

#check f x
#check f (f x)
#check f (f (f x))

/- are all applications of terms to terms.

### Abstractions

Finally, we have **abstractions**, which have the form `λ (x : τ) => e` where `τ` is a type and `e` is a term. The `x` in this expression is said to be `bound` to the abstraction. It is a dummy variable and could be renamed without any change in meaning. For example, the following are terms in the λ-calculus:  -/

#check λ (y : A) => y
#check λ (g : A → A) => λ (y : A) => g y

/- In the first example, the abstraction defines a function that simply returns its argument. In the second example, the abstraction defines a function that takes another function `g` and returns yet another abstraction that takes an object `y` and returns `g` applied to `y`.

Note that the parentheses group to the right, so the second example is equivalent to: -/

#check λ (g : A → A) => ( λ (y : A) => g y )

/- In Lean, we can also abbreviate a chained lamdba abstractions by writing: -/

#check λ (g : A → A) (y : A) => g y

/- ### Equivalence with `def`

A lambda abstraction is basically an unamed function. You could also give your functions names and use `def`. -/

def inc₁ (x : Nat) : Nat := x + 1
def inc₂ := λ x => x + 1

#eval inc₁ 3
#eval inc₂ 3
#eval (λ x => x + 1) 3

/- ### Currying

Consider the lambda abstraction -/

variable (X : Type)
variable (a : X)

#check λ (g : X → X) => λ (x: X) => g x

/- If we apply the abstraction to particular function, then we get another function. -/

#reduce (λ (g : X → X) => λ (x: X) => g x) (λ x => x)

/- This way this new function is obtained is called _Currying_ after Haskel Curry. The function can then be applied again: -/

#reduce (λ (g : X → X) => λ (x: X) => g x) (λ x => x) a


/- ## Type Derivation

All **terms have types**. These can be found using type theory's **derivation rules**:

**VAR**: Variables are declared either globally to have a given type (using Lean's variable command) or are bound in a λ-expression.

**ABST**: The type of an abstraction is always of the form A → B where A is the type of the argument and B is the type of the result.

**APPL**: If f : A → B and x : A, then the type of the application of f to x is B.

These derivation rules are applied automatically by Lean in the process of type checking using the #check directive. We can see the types Lean derives as follows. -/

def h₁ := λ (y : A) => y
def h₂ := λ (g : A → A) => λ (y : A) => g y

#check x
#check h₁
#check h₂
#check h₁ x
#check h₂ h₁               --> Example of currying
#check h₂ h₁ x

/- Note: Currying is named after the Logician Haskel Curry, who studied Electrical Engineering at MIT in the 1920s, although he eventually switched to Physics. -/

/- ## Type Errors

The typed lambda calculus disallows expressions that do not follow typing rules. For example, the following expression produces a type error -/

#check_failure λ (g : A) => λ (y : A) => g y

/- because g is not declared to be a function type and therefore cannot be applied to y.

Another example is -/

#check_failure λ (y : A) => q

/- about which Lean complains because q has not been declared in the present context.

## Judgements and Contexts

When you hover over a #check directive, Lean shows the results of the type derivation as what is called a **judgement**. It is an expression in two parts separated by a **turnstile** ⊢. For example: `#check h₁ x` produces

```
x : A
f : A → A
⊢ A
```

Before the turnstile is the **context**, a list of all the variables introduced so far. After the turnstile is the type of (h₁ x), which in this case is A. In the literature, this written:

```
{ x : A, f : A → A }  ⊢  h₁ x : A
```

which reads: "If A has type A and f has type A → A, then we can derive h₁ x has type A". In an expression such as

```
λ (y : A) => f y
```

the variable f is not bound to an enclosing lambda. In this case it is called **free**. The variable y on the other hand is `bound`. Free variables have to be declared in Lean for expressions to use them. And they have to have types consistent to how they are used. When this is done properly, you will see the free variable declarations in the context part of Lean's results.

## Beta Reduction

An abstraction can be `applied` to another term to produce a new term. This is called β-reduction. It is defined like this:

```
(λ (x:α) => M) N   —β→   M[x:=N]
```

The notation `M[x:=N]` means: take all **free** occurances of `x` in `M` and replace them with the expression N. We have to be careful that `N` does not use the variable `x` freely. Lean does this internally for us The bound version of `x` above is, internally, a completely unique variable that is just displayed as `x` for our convenience.

To apply β-reduction in Lean, you can use the #reduce directive. For example, we can see that
```
(λ (g : α → α) => λ (y : α) => g y) f   —β→   λ (y : α) => f y
```
This is obtained by replacing `g` in `g y` with `f`, as the rule describes. You can have Lean do this for you using the #reduce directive. The `#reduce` directive needs permission to be aggressive, which we can do using the `(types := true)` option. -/

#reduce (types:=true) (λ (y : A) => y) x
#reduce (types:=true) (λ (g : A → A) => λ (y : A) => g y) (λ (y : A) => y)
#reduce (types:=true) (λ (g : A → A) => λ (y : A) => g y) (λ (y : A) => y) x


/- ## Properties of the Simply Typed λ-calculus

Some interesting observations are in order. We won't prove these here, but they are good to know:

**Uniqueness of Types**: Every term has exacly one type.

**Subject Reduction Lemma**: If `M₁ : α and M₁ —β→ M₂` then `M₂ : α`. That is, beta reduction does't change the type of expressions. It just simplifies them.

**Church-Rosser Theorem**: If `M —β→ N₁` and `M —β→ N₂` then there is some `N₃` such that `N₁ —β→ N₃` and `N₂ —β→ N₃`. That is, it doesn't matter what order you β-reduce an expression's sub-expressions in, you always end up with the same term.

**Strong Normalization**: β-reduction eventually stops at an irreducible term. This is a very strong statement. In most programming languages, you can write infinite loops. But not in the simply typed λ-calculus!



## Extended Example: Church Numerals

Even though the simply typed λ-calculus looks simple, you can encode quite a bit of math with it. The goal of this next section is to show you how do do arithmetic with only what we have so far (simple arrow types and terms depending only on terms). We do this not because it is efficient -- it isn't! Instead, we want to show that the essence of arithmetic is captured by the simply typed λ-calculus.

First, we need a way to represent numbers. Church devised the following scheme, where c₀ is the **Church Numeral** for 0 and so on. -/

def α := Type

def c₀ := λ ( f : α → α ) => λ ( x : α ) => x
def c₁ := λ ( f : α → α ) => λ ( x : α ) => f x
def c₂ := λ ( f : α → α ) => λ ( x : α ) => f (f x)
def c₃ := λ ( f : α → α ) => λ ( x : α ) => f (f (f x))

/- You can check the type of a Church numeral: -/

#check c₂

/- For convenience, let's give this type a name: -/

def N := (α → α) → α → α

#check N

/- ### Arithmetic

We can define functions on numbers. For example, the successor function is defined below. -/

def succ := λ (m : N) => λ (f : α → α) => λ (x: α) => f (m f x)

/- To see how this works, let's apply succ to c₀. We omit the types to make it easier to read. Note for clarity we use the dummy variables g and y in c₀ instead of f and x.

  succ c₀ = ( λ m => λ f => λ x => f (m f x) )  ( λ g => λ y => y )
          —β—> λ f => λ x => f ( ( λ g => λ y => y ) f x )
                          [note, g is not used, so f x disappears]
          —β—> λ f => λ x => f ( ( λ y => y ) x )
          —β—> λ f => λ x => f x
          = c₁

This is a lot of work, so let's let Lean do this for us: -/

#reduce (types := true ) succ c₀
#reduce (types := true ) succ c₃

/- ### Other Operations

We can also add two numbers together: -/

def add := λ (m : N) => λ (n : N) => λ (f : α → α) => λ (x: α) => m f (n f x)

#reduce (types := true) add c₃ c₂
#reduce (types := true) add (succ c₃) (add c₁ c₂)

/- And here is multiplication: -/

def mul :=  λ (m : N) => λ (n : N) => λ (f : α → α) => λ (x: α) => m (n f) x

#reduce (types := true) mul c₃ c₂

/- We can even do a sort of if-statement: -/

def ifzero := λ (m : N) => λ (n : N) => λ (p : N) =>
              λ (f : α → α) => λ (x: α) =>
              n (λ ( y : _ ) => p f x) (m f x)

#reduce (types := true) ifzero c₂ c₀ c₃
#reduce (types := true) ifzero c₂ c₁ c₃

/- ### LEAN CAN PROVE 1+1 = 2 -/

theorem one_plus_one_is_two : add c₁ c₁ = c₂ :=
  rfl

/- You can prove this by rfl because, as we will see, two lambda expressions that beta reduce to the same thing are considered `definitionally equal`. Although this is not scalable and in fact Lean has a much more expressive type system that we will harness soon.

### Church Numerals are Inconvenient

You can define other opertations on the natural numbers in a similar fashion. It is also fairly straightforward to define Booleans and Boolean Logic, as well as a number of other basic mathematical structures.

Building up from these basic ideas to more complex mathematics is the point of Lean. Eventually, we will arrive at cutting edge mathematics in Lean. Because it is defined in terms of thee basic building blocks, we always have a proof that goes from the high level mathematica statements to the low level meaning in terms of the typed λ-calculus: That is, a proof from first princples.

That said, it will ultimately be better to define a richer set of types. For example, we'll define the natural numbers and almost every other mathematical object in Lean using what are called [Inductive Types](InductiveTypes.md).

## Type Theory Questions

Now that we have a simple programming language and a way to assign types to terms in that language, we can explore a number of problems in type theory, each with its own purpose and challenges.

**TYPE CHECKING**: In a given context, does a term M have a given type σ?
```
Γ ⊢ M : σ
```

**WELL TYPEDNESS**: Does there exist a context in which a type be assigned to a term M? Another way of saying this is "is M a legal term?"

```
? ⊢ M : ?
```

**TYPE INFERENCE**: Can M be assigned a type consistent with a given context?
```
Γ ⊢ M : ?
```

**INHABITATION**: Does there exist a term of a given type? If σ is a logical statement, then this is the question of whether σ has a proof.
```
Γ ⊢ ? : σ
```

# Type Inference

Lean is good at type inference. We can go a step further with Lean and leave out types in expressions, letting Lean infer what they must be. For example, the Church numerals can be written more consicely, skipping some of the type declarations and using multi-argument lambdas, as follows: -/

#check λ _ y => y
#check λ ( g : α → α ) y => g y
#check λ ( g : α → α ) y => g (g y)

/- We haven't said what the type of y is in these expressions. And we haven't even given the first bound variable in c₀ a name, since it isn't used in the the body of the abstraction. Lean infers that y must have type α because it is being acted upon by a function from α to α. We can also write the other operations, like multiplication, more concisely: -/

#check λ (m n : N) f x => m (n f) x

/- We can't leave out all of the type information though. Consider: -/

#check_failure λ g y => g y

/- In the above, there are any number of ways types could be assigned to g and y, so Lean complains that it can't assign types to them. So while the expression is typeable, Lean can't infer a type for it and you have to give it more information.

### Self-application is Untypeable

Dropping types for the moment, define the term
```
Ω := λ x => x x
```
and consider `Ω` applied to itself `Ω`:
```
(λ x => x x) (λ x => x x)       —β—>       (λ x => x x) (λ x => x x)
```
producing an infinite loop. Suppose you could give `M M` a type:
```
M M : σ
```
For this to work, `M` has to be a function:
```
M : τ → σ
```
But since `M` is operating on itself, `M` has to be of type `τ`:
```
M : τ
```
So `M` has two different types, which is not possible. Lean is not able to find a type for `x`. The placeholder symbol `_` is used by Lean as a way to ask the type checker to infer a type. -/

#check_failure (λ (M:_) => M M)

/- ## Propositions

Lean has a special type called `Prop` which stands for `Proposition`. It treats this type somewhat differently than all other types, but in most ways it ist just another type. -/

variable (p : Prop)
#check Prop
#check p

/- If p is of type `Prop`, then an element `hp : p` is evidence that the type p is not empty. Alternatively, you can think of hp as a `proof` of p.

Furthermore, arrow types which above denoted functions, can be thought of as denoting **implication** if `Prop` is involved.  -/

#check p → p

/- Armed with the lambda calculus and we can now prove theorems involving implication: -/

example (p : Prop) : p → p :=
  λ hp => hp

example (p q : Prop) : p → (p → q) → q :=
  λ hp => λ hpq => hpq hp

/- ## Why is it Called "Simply Typed"?

You might be asking yourself, is there a non-simply typed λ-calculus? The answer is yes! We will get there eventually. Here's a preview:

**Simple types:** Terms depend on other tems. This is what we've covered so far. For example, the body of a lambda abstraction (a term) depends on the bound variable (also a term). -/

#check (λ x : Nat => x+1) --- the term x+1 depends on the term x.

/- **Polymorphism:** Terms can depend on types. Polymorphism allows us to write functions that operate on a variety of types, instead of just a single type, by taking the type to be operated on as an argument. For example, the identity function `λ x : A => x` only operates on elements of type x. What if we wanted to define an arbitrary identity function for any type. Here is one way: -/

#check (λ α : Type => λ x : α => x) -- a polymorphic identity function.

/- A better way would be: -/

universe u
def my_id {α : Type u} (x : α) := x

#check my_id 1
#check my_id "one"
#check my_id my_id

/- Note the curly braces around `α : Type u` specify that the argument `α` is _implicit_. That is, that Lean should try to infer what it is. In the the examples `#check` statements above, Lean figures out which type the argument is, and therefor which type the overall expression is, by inspection.

**Parameterized Types:** Types can depend on types. The idea here is to build a type from other types. For example, a List type is fine, but it would nice to avoid having two make a separate data type for lists of different types of objects. In fact, Lean's standard library defines `List` as a parameterized type. You can see in the first `#check` below that making a list requires a type as an argument -/

#check List            -- Requires a type as an argument
#check List Nat        -- The type of a list of natural numbers
#check List (List Nat) -- The type of a a list of list of natural numbers

/- Lean is also good at figuring out what kind of list you are talking about in most contexts, as the following examples show. -/

#check [1,2,3]
#check ["one","two","three"]

/- **Dependent types:** Types can depend on terms. Finally, we can have types that depend on terms. For example, the type of vectors (from Lean's standard library) of natural numbers of length 10 depends on the term 10. -/

#check Vector Nat 10 -- Vectors of 10 Nats

/- **Calculus of Constructions:** If we allow all of the above in type theory, we get what is called the Calculus of Constructions, or CoC. This theory was first described by Thierry Coqrand and emboded in the Coq proof assistant, now called Rocq. Lean and other proof assistants are also based on CoC.

**Inductive Types**: Types can be defined inductively. For example, the natural numbers are defined by a base case (zero) and a successor function (succ), from which all other natural numbers can be constructed. This is discussed in more detail in the chapter on [Inductive Types](./InductiveTypes.md).

**Quotients**: Quotients of types via equivalence relations. For example, a real number is defined to be the set of all Cauchy sequences of rational numbers that converge to it. That is, the reals are the quotient of the set of Cauchy Sequences by Cauchy equivalence. This is discussed in more detail in the chapter on [Quotients](./Quotients.md).

## Looking ahead: the Curry-Howard Correspondence

The most important problem in using type theory for proofs is INHABITATION, followed by TYPE CHECKING. To motivate why, we will see later the following remarkable fact, called the Curry-Howard corresponence, which says that in the judgement Γ ⊢ M : σ,

- Γ can be considered a set of givens or assumptions
- σ can be considered a mathematical statement like a theorem or lemma
- M can be considered a proof of the theorem assuming the statements in Γ.

Thus, type checking amounts to checking that M is a proof of σ, which is a relatively straightfoward problem and we have seen that Lean is quite good at it. This is why tools like Lean are called `proof assistants`. They check to make sure your proofs are correct.

On the other hand, type inhabitation amounts to finding a proof of σ. This is a very difficult problem, essentially the job of the working mathematician. From a computational point of view, finding a proof means searching over terms M until one finds one that has type σ. Depending on how expressive the programming language for terms is, this can either be a computationally intractable problem (meaning search is the best you can do) or it can be a computationally unsolvable problem (meaning there may not be an algorithm that is guaranteed to find an M of type σ). Both of these observations are job security for mathematicians!

Going a step further, we'll see that an abstraction
```
λ p : σ => q
```
which may have type
```
σ → τ
```
is the general form of a proof of the statement σ → τ where → means "implies". It can be thought of as a transformation taking a proof of σ, which one assumes is available, and returning a proof of τ, which is thought of as a goal to be proved. Writing the details of what q is amounts to programming.

As a computer scientist myself it is very satisfying to know that programming functions with given type specifications is _the same thing as_ proving theorems!

This idea is not merely cute. By building on it, as Lean and similar tools do, one can enocde an astonishingly large set of all of mathematics, and presumably knowledge in general. We'll learn how to take advantage of the Curry-Howard corresponence soon.

## REFERENCES

Alonzo Church
[An Unsolvable Problem of Elementary Number Theory](https://www.jstor.org/stable/2371045).
American Journal of Mathematics, 1936.

Haskell B Curry
[The Inconsistency of Certain Formal Logics](https://www.cambridge.org/core/journals/journal-of-symbolic-logic/article/abs/inconsistency-of-certain-formal-logics/FF38B653569E479408EC4DDD26DD7918).
The Journal of Symbolic Logic, 1942.

Alonzo Church
[A formulation of the simple theory of types](http://www.classes.cs.uchicago.edu/archive/2007/spring/32001-1/papers/church-1940.pdf).
Journal of Symbolic Logic, 1940

Uwe Nestmann and Students
[The Lambda Cube Unboxed](https://www.youtube.com/playlist?list=PLNwzBl6BGLwOKBFVbvp-GFjAA_ESZ--q4).
YouTube, 2020


-/
