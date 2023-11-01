/-
Copyright (c) 2023 Leonardo de Moura. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Leonardo de Moura
-/

/-!
Symbolic evaluator.

Given a term `e`, it computes a pair `(eNew, pr)` such that `pr : e = eNew`.
Moreover, we want the proof to be efficiently checked by the kernel.
Here efficient means if it takes `n` seconds to reduce `e`, then it
should take `k*n` to check `pr`, where `k` is a small constant.

- We do not want to change how we handle substitution in the kernel.
We want to keep it simple, and ensure simple external checkers can also check our proofs.

- We want to prevent the delta-reducing big definitions. Some tricks:
  - Use equation lemmas.
  - Use auxiliary definitions to generate more "compact versions" of the equation lemmas.
    For example, suppose we have
    ```
    theorem f_eq : f x = if c[x] then T[x] else E[x]
    ```
    where `T[x]` and `E[x]` are big terms. The theorem above can be rewritten as
    ```
    def f_aux₁ x := T'[x]
    def f_aux₂ x := E'[x]
    theorem f_eq' : f x = if c[x] then f_aux₁ x else f_aux₂ x
    ```
    where `T'[x]` and `E'[x]` are `T[x]` and `E[x]` after recursively creating auxiliary
    definitions for its nested terms.

- We use `ShareCommon` to deduplicate terms.

- We cache results using pointer-equality.

- We handle `let`-expressions by preprocessing them. We expand all non-dependent let-expressions.
  The remaining ones are processed using a theorem similar to `funext`.

- When creating auxiliary declarations, we should float non-dependent `let`-declarations.

- We need a notion of "value", and it should be user extensible.
  We must have builtin support for:
  - Constructors where the fields are values.
  - Literals.
  - Lambdas.
  - Arrays. We don't want to treat them as lists.
  - Char. We want to keep representing them as `Char.ofNat`
  - String. We should use auxiliary theorems to compute with the builtin String operations.
  - UIntX. Do we need special support?

- We have builtin support for reducing builtin definitions on Arrays, Strings, Chars, etc.

- We should have support for computing with propositions even when they are not decidable.
  In `if`-expressions, we should reduce the `Decidable` instance instead of the p

- We should support `csimp` like theorems to replace the actual implementation during symbolic
  evaluation.

- Users may define their own extensions that are triggered by patterns (like in `norm_num`).

- When reducing an application `f a`. We first try user extensions. If no extension is applicable,
  we try call-by-value or call-by-name (it is configurable by the user).

- When using call-by-value, we first reduce the arguments based on the congruence lemmas available
for the function, and then apply the compact equation lemmas.

- For call-by-name, we use the compact equation lemmas.

- For nested lambda expressions, we must preprocess them as we process equation lemmas,
  and add auxiliary declarations to reduce beta-reduction cost.

- We have builtin support for if-then-else and match-expressions.

- We want `simp` to handle nested ground terms.

-/
