import Pom.Order.FinApprox

namespace Pom

variable {l : Type} [DCPO l] [OrderBot l] [ScottCompact l]

open OmegaCompletePartialOrder

noncomputable def ext {X : Type} [OmegaCompletePartialOrder X]
    (f : Pomfin l → X) (hf : Monotone f) (p : Pom l) : X :=
  ωSup {
    toFun n := f (p.trunc n)
    monotone' _ _ hle := hf (trunc_mono (le_refl _) hle)
  }

lemma upper_bound_of_compact_pom (c : Chain (Pom l)) (n : ℕ) :
    ∃ i, (ωSup c).trunc n ≤ (c i).trunc n := by
  have ⟨c', hc⟩ := exists_lpo_chain_of_pom_chain c
  have ⟨i, hle⟩ := upper_bound_of_compact c' n
  refine ⟨i, (ωSup c').trunc n, ?_, (c' i).trunc n, ?_, ?_⟩
  · refine Pomfin.val_mem_to_pom.mp (lpo_trunc_mem ?_)
    have ⟨hle, hge⟩ := lpo_chain_pom_chain_lub hc
    simp only [upperBounds, Set.mem_range, forall_exists_index, forall_apply_eq_imp_iff,
      Set.mem_setOf_eq, lowerBounds] at hle hge
    refine le_antisymm ?_ ?_
    · exact ωSup_le _ _ hle
    · exact hge (le_ωSup _)
  · exact Pomfin.val_mem_to_pom.mp (lpo_trunc_mem (hc i))
  · exact Lpo.trunc_le_trunc hle

theorem ext_continuous {X : Type} [OmegaCompletePartialOrder X] {f : Pomfin l → X}
    (hf : Monotone f) : ωScottContinuous (ext _ hf) := by
  have hmono : Monotone (ext f hf) := by
    intro p q hle; refine ωSup_le_ωSup_of_le ?_
    intro n; use n; exact hf (trunc_mono hle (le_refl _))
  refine ωScottContinuous.of_monotone_map_ωSup ⟨hmono, ?_⟩
  intro c; refine le_antisymm ?_ ?_
  · refine ωSup_le _ _ ?_; intro n
    have ⟨i, hi⟩ := upper_bound_of_compact_pom c n
    refine (hf hi).trans (le_trans ?_ (le_ωSup _ i))
    refine le_of_eq_of_le ?_ (le_ωSup _ n); rfl
  · refine ωSup_le _ _ ?_; intro i
    simp only [Chain.coe_map, OrderHom.coe_mk, Function.comp_apply]
    exact hmono (le_ωSup _ _)

noncomputable def ext₂ {X : Type} [OmegaCompletePartialOrder X]
    (f : Pomfin l → Pomfin l → X)
    (hf : ∀ {p p' q q'}, p ≤ p' → q ≤ q' → f p q ≤ f p' q') (p q : Pom l) : X :=
  ωSup {
    toFun n := f (p.trunc n) (q.trunc n)
    monotone' _ _ hle := hf (trunc_mono (le_refl _) hle) (trunc_mono (le_refl _) hle)
  }

omit [ScottCompact l] in
theorem ext₂_monotone {X : Type} [OmegaCompletePartialOrder X]
    {f : Pomfin l → Pomfin l → X}
    {hf : ∀ {p p' q q'}, p ≤ p' → q ≤ q' → f p q ≤ f p' q'} {p p' q q' : Pom l}
    (hle : p ≤ p') (hle' : q ≤ q') :
    ext₂ f hf p q ≤ ext₂ f hf p' q' := by
  refine ωSup_le_ωSup_of_le ?_; intro n; use n
  refine hf ?_ ?_ <;> refine Pom.trunc_mono ?_ (le_refl _) <;> assumption

theorem ext₂_continuous {X : Type} [OmegaCompletePartialOrder X]
    {f : Pomfin l → Pomfin l → X}
    {hf : ∀ {p p' q q'}, p ≤ p' → q ≤ q' → f p q ≤ f p' q'} {c c' : Chain (Pom l)} :
    ext₂ f hf (ωSup c) (ωSup c') = ωSup {
      toFun n := ext₂ f hf (c n) (c' n)
      monotone' _ _ hle := ext₂_monotone (c.monotone' hle) (c'.monotone' hle)
    } := by
  refine le_antisymm ?_ ?_
  · refine ωSup_le _ _ ?_; intro n
    have ⟨i, hi⟩ := upper_bound_of_compact_pom c n
    have ⟨j, hj⟩ := upper_bound_of_compact_pom c' n
    refine le_trans ?_ (le_ωSup _ (max i j))
    refine le_trans ?_ (le_ωSup _ n); refine hf ?_ ?_
    · refine hi.trans (Pom.trunc_mono ?_ (le_refl _))
      exact c.monotone' (Nat.le_max_left _ _)
    · refine hj.trans (Pom.trunc_mono ?_ (le_refl _))
      exact c'.monotone' (Nat.le_max_right _ _)
  · refine ωSup_le _ _ ?_; intro n
    refine ext₂_monotone ?_ ?_ <;> exact le_ωSup _ _

lemma continuous_of_eq_ext₂ {X : Type} [OmegaCompletePartialOrder X]
    {f : Pom l → Pom l → X}
    (hmono : ∀ {p p' q q'}, p ≤ p' → q ≤ q' → f p q ≤ f p' q')
    (heq : f = ext₂ (fun p q ↦ f p.to_pom q.to_pom) hmono)
    (c₁ c₂ : Chain (Pom l)) :
    f (ωSup c₁) (ωSup c₂) = ωSup {
      toFun n := f (c₁ n) (c₂ n)
      monotone' _ _ hle := hmono (c₁.monotone' hle) (c₂.monotone' hle)
    } := by
  refine (congrFun₂ heq _ _).trans <| ext₂_continuous.trans (congrArg _ ?_)
  ext n; exact congrFun₂ heq.symm _ _

end Pom
