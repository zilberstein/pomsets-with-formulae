import DomainTheory.OmegaCompletePartialOrder.Instances

import Pom.Linearization
import Pom.Lpo.Linearization.Guard
import Pom.Operations.Guard

open Linearization

namespace Pom
open OmegaCompletePartialOrder

lemma lin_guard {t : Type → Type} {s act test : Type}
    [Linearizable t s]
    [∀ {β : Type}, OmegaCompletePartialOrder (t β)] [∀ {β : Type}, OrderBot (t β)]
    [DCPO act] [ScottCompact act] [Sem act s (t s)]
    [DCPO test] [ScottCompact test] [Sem test s (t Bool)]
    (p q : Pom (Label act test)) (b : test) :
    (lin (guard (Label.test_ne_bot b) p q) : s → t s) =
    fun σ ↦ Sem.sem b σ >>= fun r ↦ bif r then lin p σ else lin q σ := by
  obtain ⟨α, β, x, hx, hx', hd, rfl, rfl, hmem⟩ := exists_rep_guard (Label.test_ne_bot b) p q
  rw [guard_mk hx hx' hd, lin_mk]
  rw [Chain.ωSup_shift]; simp only [Chain.shift, DFunLike.coe]
  conv in Lpo.trunc _ _ => exact Lpofin.guard_trunc _
  conv in Lpofin.lin _ => exact Lpofin.lin_guard
  ext σ; rw [ωSup_apply]; simp only [DFunLike.coe]
  let c : Chain (Bool → t s) := {
    toFun n r := bif r then (α.trunc n).lin σ else (β.trunc n).lin σ
    monotone' _ _ hle r := by
      cases r <;> simp only [cond_true, cond_false] <;>
        exact Lpofin.lin_mono (Lpo.trunc_mono (le_refl _) hle) _
  }
  conv =>
    lhs; exact (ContinuousMonad.bind_continuous (c₁ := Chain.const (Sem.sem b σ)) (c₂ := c)).symm
  refine congrArg₂ _ (Chain.ωSup_const _) ?_
  ext r; rw [ωSup_apply]; simp only [c, DFunLike.coe]
  cases r <;> (simp only [cond_true, cond_false]; symm; exact congrFun (lin_mk _) _)

end Pom
