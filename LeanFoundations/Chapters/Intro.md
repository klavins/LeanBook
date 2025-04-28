
#
#
#
#
#
#
#                                  EE546 - W25
#
#                     `Knowledge Representation and Reasoning`
#                                  `Introduction`
#
#                 DEPARTMENT OF ELECTRICAL AND COMPUTER ENGINEERING
#                            UNIVERISITY OF WASHINGTON
#                               PROF.  ERIC KLAVINS
#
#                                  WINTER 2025
#
#
#
#
#
#
#
#





# INTRODUCTIONS

We'll go around the room an introduce ourselves.

I'll talk about why I want to teach this course.
























# WHAT IS THIS COURSE ABOUT?

  Philisophically: 
    - Represent and reason about knowledge symbolically
    - Encourage a high standard for how computers will eventually think

  Practically: 
    - Learn the formal foundations of mathematics through type theory
    - Learn to program in Lean
    - Learn to prove theorems with Lean
    - Apply these tools to a variety of engineering problems

  My Interests:
    - Foundations of mathematics
    - Correctness of programs
    - Antidisinformation    












# YOUR INTERESTS (FROM SURVEY)

- Mathematical proof techniques for ML
- Motion planning robotics
- Robotic reasoning.
- What AI can and can't do in math/engineering
- Trust-worthy AI systems
- Neuro-symbolic learning
- Control theory and its different uses. 
- Programming and/or critical thinking 
- Hardware/circuit validation
- Basic theory















# DETAILS

  Course Materials

  - Canvas: https://canvas.uw.edu/courses/1789473?for_reload=1
  - Github: https://github.com/klavins/EE546_W25 

  Structure

  - Lecture + in class work

  - Weekly(ish) homeworks (with me grading everything, yikes)
    - Worth 2/3 of the grade
    - 99% Lean 
    - The first real homework is posted and due Monday
      - https://github.com/klavins/EE546_W25/blob/main/EE546_W25/Homework/HW1.lean
    - Also, you need to install Lean by Thursday

  - A project
    - More details to come


















# WHAT IS KNOWLEDGE?

In philosophy, knowledge has many definitions, all of which are fairly loose, but which mainly amount to `cognitive states or beliefs about the world that correspond to actual facts`. The latter half of this definition distiguishes such cognitive states from unsubstantiated beliefs. 

Alternatively, beliefs can be justified by observation, meaning that nothing in the knower's experience contradicts the belief, whether or not the belief is actually true. 

Thus, we have three notions to consider:

  - Belief
  - Fact
  - Justification














# COMBINATIONS OF BELIEFS, FACTS, AND JUSTIFIACTIONS

- `A belief may be both true and justified`. This means the subject (holder of the belief) has empirical evidence supporting their belief, and that the belief corresponds to an actual fact. For example, consider the belief "It is raining". If the subject believes it is raining, has observed that it is raining, and it is in actual fact raining, then they have a justfied, factual belief. 

- `A belief may be false and justified`. Someone may have tricked the subject into thinking it is raining, for example by arriving to work wearing a wet raincoat prepared using a garden hose. In this case, the subject is justified in believing it is raining, even though in fact it is not raining.

- `A belief may be true and unjustified`. The subject may simply believe it is raining, with no evidence in support of the belief whatsover, while at the same time it happens to be raining. 

- `A belief may be untrue and unjustified`. The subject may believe it is raining without any evidence and in may in fact not be raining. 

  Q: What are some engineering examples in these four categories?








# BELIEFS

One may ask `what is a belief`. Here, we have defined it as a cognitive state. But what is that? If the brain were a computer, we might say that a cognitive state is a `data structure` of some sort in the brain describing the belief. For example, the computer/brain may be running a simulation of the world in which it is raining -- in the simulation! 

Alternatively, we could adopt an `empirical` view, meaning that if the subject is questioned about their belief, they make statements consistent with the belief. So, if asked whether it was raining, they would say "yes". 

In either of these cases, it becomes evident that to really understand what it means to know something, one must first understand what a known thing is, either as a computer state or a liguistic/syntactic element. This is the `knowledge representation` problem, although perhaps it ought to be called the `belief representation` problem since we will develop formalisms allowing us to represent beliefs whether they are justified or not, and whether they are true or not.

  Q: Do you think the brain uses data structures to represent knowledge?












# EMPERICAL EVIDENCE

What does `justified` mean? We described `emperical evidence` and `observations`. These notions essentially describe how we come to believe, for example, a "law" of science. We keep making observations, often as about the outcome of experiments, and if they do not contradict our belief (the hypothesis), then we might begin to call that belief a "law". This doesn't mean the law is true! Just that we have never observed enough evidence to the contrary. 

  Q: What is an example of a scientific law? What is the evidence for it?



















# ARGUMENT OR PROOF (THE SUBJECT OF THIS COURSE)

The notion of `justified` can have another meaning, which is that the belief follows from other beliefs via a sound argument. For example, one might believe the sidewalk is wet *because* it is raining. Whether it actually is raining is one question, but the belief that "raining implies wet sidewalks" is a belief in a new statement that is justified because of some model of the physical world and a logical inference made with respect to that model. 

This type of knowledge is most similar to mathematics. For example, from the definition of prime numbers it follows (via Euclid's theorem) that there are an infinite number of of them. The `proof` of the theorem is the `justification` in this case. 

Thus, justifications can be either empirical observations or logical arguments. The former may correspond to actual facts or not, while the latter definitely do correspond to actual facts. 

  Q: What is an example of a logical justification (outside of mathematics)?













# FACTS

What then is a `fact`? 

Without getting too philosophical, an `empirical` fact is a statement about the true nature of the universe. We mere humans may never know which of our beliefs are actual facts, as we are limited to our senses, which can deceive us. 

Alternatively, a `logical` fact is a statement that follows from other statements that are assumed true. This sort of fact can be checked, as with a mathematical proof. 

  - Q: What is an example of an emperical fact?
  - Q: What is an example of a logical fact?

















# KNOWLEDGE REPRESENTATION

The first task in this course is to understand how to `represent` beliefs, emperical evidence, logical arguments, and facts. And since it is an engineering course, our goal will be to make such representations computer-based so that we can manipulate these notions, enabling our computers to form their own beliefs and justifications.






















# KINDS OF KNOLWEDGE

- Embodied knowledge
    - E.g. how to walk (a neuro-genetically encoded control algorithm)

- Scientific knowledge
    - E.g. F = ma or E = mc^2
    - Mathematical models and simulations

- Deductive knowledge
  - Knowledge that arises from observations through reasoning

- Engineering knowledge
    - Recipes, procedures
    - Schematics, diagrams
    - Computer code

- Mathematical knowledge
    - Knowledge that arises from assumptions through reasoning
    - E.g. there an infinite number of prime numbers

Q: What are examples of each of these types of knowledge?

Q: Can you think of other types of knowledge?






# HOW IS KNOLWEDGE REPRESENTED?

- Genetically 
- Weights on neurons in our brains
- Weights in an artifical neural network
- As drawings and pictures and schematics
- Graphs and networks
- Probabilistically

- Syntactically
    - Natural language
    - Computer programming languages
    - Specification languages (Verilog, HTML, SVG, STL)
    - Logic: propositional, first order, second order, specialy (e.g. temporal logic)

THESIS: `Syntax subsumes the all other categories` --> In principle, you can write a simulation of pretty much anything, and that simulation would be written with code.

  Q: To what extent does an LLM know anything?
  Q: What is the primary source of knowledge for an LLM like Chat GPT?










# CHALLENGES

  - `Language Design`: Defining a language that is expressive enough to represent ideas, but not as ambiguous as natural langauge. 

  - `Reasoning`: How do deduce new true statements from existing true statements? How do you check your results? How do you automate reasoning?

  - `Soundness`: How do you ensure that everything provable is actually true?

  - `Completness`: How do you ensure that everythying true is provable?

  - `Decidability`: How do you ensure that reasoning can be done effectively on a computer?

  - `Nonmonotonicity`: As you add more knowledge to a knolwedge base, you have do deal with possible contradictions, resulting in revised beliefs that are so highly qualified as to be useless.

  - `The frame problem`: When you formally state that something changes, you also have to formally state that nothing else changes (https://plato.stanford.edu/entries/frame-problem/)

Q: How do LLMs score on all these challenges?






# BUT, REALLY, WHAT IS THIS COURSE ABOUT? 

  An introduction to formal logic
    - Propositional Logic
    - First Order Logic
    - Higher Order Logic

  A deep dive into the foundations of mathematics
    - Type Theory
    - The Curry-Howard Isomorphism
    - Automated theorem provers / checkers

  Good Old Fashioned AI (Robotics, Natural Language, ...)
    
  Reasoning About Time
    - Planning
    - Program verification

  Examples of formalizing mathematics
    - Numbers
    - Analysis
    - Algebraic structures

  Other Topics : There are a millions directions to go














# PROJECTS

  Scope: Produce a draft of a six page technical conference paper with some really nice Lean code as the core contribution.

  Ideas: 

    - Formally specify an engineering artifact and check for bugs
      - e.g. Show a robot algorithm converges
      - e.g. Show an embedded system is safe
      - e.g. Show a bit of code is cyber-secure

    - Formally specify a chapter of an engineering textbook
      - e.g. Control theory
      - e.g. Signal processing
      - e.g. Machine learning

    - Formally specify a scientifc theory
      - e.g. Quantum electrodynamics

    - Connect an LLM to Lean to make a proof assistant
    - Automaticaaly generate proofs that LLM outputs are correct
    - Build a new proof tactic (an algorithm for helping prove stuff)

  We'll return to this list as you learn more about Lean.






# SO, WHY NOW?

  - Theorem provers have become so powerful that soon all of math will be taught with them.

  - Disparate tools used in AI, KR, Model Checking, and elsewhere are subsumed by Lean.

  - LLM based reasoning is unreliable, toxic, and horrible. The need for alternatives has never been more important.
  
  - Neuro-symbolic approaches may help with
    - Correctness
    - Explainability
    - Provenance

  - If you have always struggled to really understand math, Lean is an absolutely amazing self-learning tool. 











# FIND OUT WHAT PEOPLE ARE DOING

- Science: https://leanprover.zulipchat.com/#narrow/channel/395462-Natural-sciences

- ML: https://leanprover.zulipchat.com/#narrow/channel/219941-Machine-Learning-for-Theorem-Proving

- Safety of AI: https://leanprover.zulipchat.com/#narrow/channel/113486-announce/topic/Guaranteed.20Safe.20AI.20Seminars

- Crazy high level maths: https://leanprover-community.github.io/blog/posts/lte-final/

- Math projects: https://leanprover-community.github.io/papers.html

- Various scale projects both small and huge: https://leanprover-community.github.io/lean_projects.html














































# FURTHER RESOURCES

- Russel and Norvig's AI Textbook: 
  https://aima.cs.berkeley.edu/

- Theorem Provers: 
  https://www.scientificamerican.com/article/ai-will-become-mathematicians-co-pilot/

- LLMS + Theorem Provers: 
  https://www.wired.com/story/google-deepmind-alphaproof-ai-math/

- Theorem Provers and Anti-Disinformation: 
  https://www.nytimes.com/2024/09/23/technology/ai-chatbots-chatgpt-math.html
