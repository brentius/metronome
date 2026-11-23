namespace Metronome

/-- State sampled before cycle `n`, with input 0 applied on the first transition. -/
def run (next : S → I → S) (inputs : Nat → I) (initial : S) : Nat → S
  | 0 => initial
  | n + 1 => next (run next inputs initial n) (inputs n)

theorem run_succ (next : S → I → S) (inputs : Nat → I) (initial : S) (n : Nat) :
    run next inputs initial (n + 1) = next (run next inputs initial n) (inputs n) := rfl

theorem invariant_after_first (next : S → I → S) (inputs : Nat → I)
    (initial : S) (invariant : S → Prop)
    (first : invariant (next initial (inputs 0)))
    (preserved : ∀ state input, invariant state → invariant (next state input)) (n : Nat) :
    invariant (run next inputs initial (n + 1)) := by
  induction n with
  | zero => exact first
  | succ n ih => exact preserved _ _ ih

theorem run_congr {next reference : S → I → S} (equiv : ∀ s i, next s i = reference s i)
    (inputs : Nat → I) (initial : S) (n : Nat) :
    run next inputs initial n = run reference inputs initial n := by
  induction n with
  | zero => rfl
  | succ n ih => rw [run_succ, run_succ, equiv, ih]

end Metronome
