import RegretKappa.MainStatement
import RegretKappa.LowerSharpCheck.IndepL

/-!
# Theorem 4.1 and the main theorem against a formalization written separately

`RegretKappa/LowerSharp/Statement.lean` and `RegretKappa/MainStatement.lean` against
`RegretKappa/LowerSharpCheck/IndepL.lean`, a separately written formalization of the same text.
The quantities agree (`j0_eq`, `level_eq`, `c1_eq`, `bT_eq`, `boundU_eq`), and so do
the propositions (`adv_iff`, `onePlay_iff`, `main_iff`, `bounded_iff`). The last two concern the
forms with `b(T)` and `U(T)`, `MainTheoremChain` and `MainBoundedFeaturesChain`, the text of the
main theorem and of Corollary 5.1 that the separate formalization was written from; the closed
forms are compared in `RegretKappa/LowerSharpCheck/EquivM.lean`. The two readings of the
simplified forms differ in shape: ours is the chain of the paper
`b(T) ≥ form₁ ≥ form₂`, the separate one the two bounds `b(T) ≥ form₁` and `b(T) ≥ form₂`; the first
implies the second (`simplified_imp`), and they are equivalent given `form₁ ≥ form₂`
(`simplified_iff_of`).
-/

namespace RegretKappa.LowerSharpCheck

open Real RegretKappa.LowerSharp

theorem j0_eq (T : ℕ) : IndepL.j0 T = j0 T := rfl

theorem level_eq (T : ℕ) : IndepL.L T = level T := rfl

theorem c1_eq : IndepL.c1 = c1 := by
  rw [IndepL.c1, c1, Jc, ← Real.exp_nat_mul]
  norm_num

theorem bT_eq (T : ℕ) : IndepL.b T = bT T := by
  rw [IndepL.b, bT, c1_eq]
  rfl

theorem boundU_eq (T : ℕ) : IndepL.U T = boundU T := rfl

theorem adv_iff : LowerSharpAdv ↔ IndepL.Adversary := by
  simp only [LowerSharpAdv, IndepL.Adversary, bT_eq, T0]

theorem onePlay_iff : LowerSharpBound ↔ IndepL.OnePlay := by
  simp only [LowerSharpBound, IndepL.OnePlay, bT_eq, T0]

theorem simplified_imp : LowerSharpSimplified → IndepL.Simplified := by
  intro h
  simp only [IndepL.Simplified, bT_eq]
  exact ⟨fun T hT => (h T hT).1, fun T hT => (h T hT).2.trans (h T hT).1⟩

theorem simplified_iff_of
    (h : ∀ T : ℕ, T0 ≤ T → 3 * log T - 2 * log (log T) - 15.2 ≤
      3 * log T - log (log T) - 2 * log (log (log T) + 2.1) - 14.6) :
    LowerSharpSimplified ↔ IndepL.Simplified := by
  refine ⟨simplified_imp, fun hI T hT => ⟨?_, h T hT⟩⟩
  have := hI.1 T hT
  rwa [bT_eq] at this

theorem main_iff : MainTheoremChain ↔ IndepL.Main := by
  simp only [MainTheoremChain, IndepL.Main, bT_eq, boundU_eq, boundL, T0, KappaEqThree]

theorem bounded_iff : MainBoundedFeaturesChain.{0} ↔ IndepL.Bounded := by
  simp only [MainBoundedFeaturesChain, IndepL.Bounded, bT_eq, boundU_eq, boundL, T0, mul_comm (bT _)]
  constructor
  · intro h
    exact ⟨fun B hB T hT => (h B hB T hT).1, fun B hB T hT => (h B hB T hT).2⟩
  · intro h B hB T hT
    exact ⟨h.1 B hB T hT, h.2 B hB T hT⟩

end RegretKappa.LowerSharpCheck
