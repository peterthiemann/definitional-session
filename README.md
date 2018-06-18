# Typed Definitional Interpreter for a Functional Language with Session Types #

This repository contains the Agda implementation. It compiles with Agda 2.5.3 and works with the standard library version 0.13.
The development is structured in several modules and may be read in the following order.

  * `Typing.agda` types, session types, equivalence, subtyping, duality, along with some lemmas
  * `Syntax.agda` typed expressions (A normal form), some auxiliary lemmas
  * `Global.agda` session contexts, splitting, inactive, (very technical) splitting lemmas
  * `Channel.agda` valid channel references, several versions of vcr-match for different rendezvous
  * `Values.agda` values, environments, and auxiliary lemmas
  * `Session.agda` continuations, commands, interpreter for expressions `run`, lifting, thread pools, several matchWait functions
  * `Schedule.agda` step function and interpreter for thread pools `schedule`, **main entry point** `start`
  
Furthermore, there are some auxiliary modules.

  * `DSyntax.agda` syntax in direct style
  * `ANF.agda` transformer from direct style DSyntax to Syntax
  * `Examples.agda` several example programs exercising progressively difficult features
  * `Run.agda` running a couple of examples (**very** inefficient)
  * `ProcessSyntax.agda` typed syntax for process terms
  * `ProcessRun.agda` definitions to run a process term + many auxiliary lemmas
