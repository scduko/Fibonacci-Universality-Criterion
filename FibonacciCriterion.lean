import FibonacciCriterion.Criterion.Theorem
import FibonacciCriterion.Example

/-!
# Fibonacci-universality criterion

The root module; it imports every module of the formalization. The main
theorem is `FibonacciCriterion.fibonacci_criterion`
(Theorem 1.1), in `FibonacciCriterion.Criterion.Theorem`.

The proof has two parts:

* `FibonacciCriterion.Criterion.Proof` proves the criterion from the
  classical results collected in `FibonacciClassicalInputs`
  (`FibonacciCriterion.ClassicalInputs.Definitions`);
* `FibonacciCriterion.ClassicalInputs.Theorems` proves those classical
  results.
-/
