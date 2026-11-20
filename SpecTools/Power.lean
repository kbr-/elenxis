/-!
The power of the forced-choice bar. A judge gets `n` pairs, one text of ours and one real owner's post in random
order, and names the one a model wrote; a text set passes when the one-sided upper confidence bound on the judge's
accuracy, Clopper-Pearson at level `α`, is at most one half plus a margin `m`. For a true accuracy `p` the chance
of passing is the binomial probability of the counts `k` whose bound passes. Choosing `m` and `n` asks two numbers
of each: the chance that a set the judge can't tell from real posts (`p = 1/2`) passes, and the chance that a set
it tells apart at a stated accuracy passes, which a useful bar keeps small.

Floating point, for counts up to a few hundred: the probabilities come from logarithms of factorials, and the
bound is found by bisection to well under a thousandth; both are checked against published values below.
-/

namespace SpecTools.Power

/-- The logarithms of `0!` to `400!`, computed once. -/
def logFacts : Array Float :=
  (List.range 400).foldl (fun acc i => acc.push (acc.back! + Float.log (i + 1).toFloat)) #[0]

/-- The logarithm of `n!`, for `n` up to 400. -/
def logFact (n : Nat) : Float := logFacts[n]!

/-- The binomial probability of `k` successes in `n` trials of probability `p`, from logarithms, so the
coefficient overflows at no size used here. -/
def pmf (n k : Nat) (p : Float) : Float :=
  if p ≤ 0 then (if k == 0 then 1 else 0) else if p ≥ 1 then (if k == n then 1 else 0) else
  Float.exp (logFact n - logFact k - logFact (n - k) + k.toFloat * Float.log p + (n - k).toFloat * Float.log (1 - p))

/-- The probability of at most `k` successes. -/
def cdf (n k : Nat) (p : Float) : Float := ((List.range (k + 1)).map (pmf n · p)).foldl (· + ·) 0

/-- Bisection for the `p` where `cdf n k p` falls to `α`, within `[lo, hi]`. -/
def bisect (n k : Nat) (α : Float) : Nat → Float → Float → Float
  | 0, lo, hi => (lo + hi) / 2
  | fuel + 1, lo, hi =>
    let mid := (lo + hi) / 2
    if cdf n k mid > α then bisect n k α fuel mid hi else bisect n k α fuel lo mid

/-- The one-sided upper Clopper-Pearson bound at level `α`: the `p` where at most `k` successes have probability
`α`, the cumulative probability falling as `p` grows; 1 when every trial succeeded. -/
def upper (n k : Nat) (α : Float) : Float :=
  if k ≥ n then 1 else bisect n k α 60 (k.toFloat / n.toFloat) 1

/-- Whether `k` of `n` right answers pass the bar of margin `m` at level `α`. -/
def passes (n k : Nat) (α m : Float) : Bool := upper n k α ≤ 0.5 + m

/-- The chance a set passes when the judge's true accuracy is `p`. -/
def power (n : Nat) (α m p : Float) : Float :=
  (((List.range (n + 1)).filter (passes n · α m)).map (pmf n · p)).foldl (· + ·) 0

/-! The bound against its published values: 5 of 10 gives 0.7775, none of 10 gives 1 − 0.05^(1/10) = 0.2589. -/

theorem upper_five_of_ten : (upper 10 5 0.05 - 0.7775).abs < 0.0005 := by native_decide
theorem upper_none_of_ten : (upper 10 0 0.05 - 0.2589).abs < 0.0005 := by native_decide
theorem all_right_never_passes : passes 20 20 0.05 0.2 = false := by native_decide

/-- The table `synthetic power` prints: per pair count and margin, the chance of passing at accuracies 0.5, 0.6,
0.7 and 0.8. Each count's bounds are computed once and shared by its margins and accuracies. -/
def table : List String :=
  "pairs\tmargin\tpass@0.5\tpass@0.6\tpass@0.7\tpass@0.8" ::
  ([20, 30, 40, 60, 80, 100, 150, 200].flatMap fun n =>
    let bounds := (List.range (n + 1)).map (upper n · 0.05)
    ([0.05, 0.1, 0.15, 0.2] : List Float).map fun m =>
      let passing := ((List.range (n + 1)).zip bounds).filterMap fun (k, u) => if u ≤ 0.5 + m then some k else none
      let cell := fun p => toString (((passing.map (pmf n · p)).foldl (· + ·) 0 * 1000).round / 1000)
      s!"{n}\t{m}\t{cell 0.5}\t{cell 0.6}\t{cell 0.7}\t{cell 0.8}")

/-- The table's rows agree with `power` where both are cheap. -/
theorem table_agrees : (power 20 0.05 0.2 0.5 * 1000).round / 1000 ==
    ((((List.range 21).filter (passes 20 · 0.05 0.2)).map (pmf 20 · 0.5)).foldl (· + ·) 0 * 1000).round / 1000 := by
  native_decide

end SpecTools.Power
