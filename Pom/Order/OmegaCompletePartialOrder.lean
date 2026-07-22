import Pom.Order.FinApprox.Koenig

open Cardinal OmegaCompletePartialOrder

def LpoChain (l : Type) [PartialOrder l] [OrderBot l] (c : Chain (Pom l)) (n : ℕ) :=
  { f : Fin n → Lpo l //
    Monotone f ∧ ∀ k, (f k).nodes.compl.Infinite ∧ f k ∈ c k }

namespace LpoChain

lemma exists_extensible_perm {X Y : Set Node} (hinf : X.compl.Infinite) (hsub : X ⊆ Y) :
    ∃ Z : Set Node, ∃ e : Y ≃ Z, Z.compl.Infinite ∧ PermExt (Equiv.refl X) e := by
  have hc : Cardinal.mk X.compl = Cardinal.mk (Bool × Node) := by
    refine Eq.trans ?_ (Eq.symm ?_) (b := ℵ₀)
    · exact @Cardinal.mk_eq_aleph0 _ _ hinf.to_subtype
    · exact Cardinal.mk_eq_aleph0 _
  have ⟨e⟩ := Cardinal.eq.mp hc
  -- U witnesses the permutation of the remaining available nodes into two countably infinite
  -- sets of nodes, one which can be used now and the other to be left available
  let U i : Set Node := Subtype.val ∘ e.symm '' Set.prod {i} Set.univ
  have hU i : (U i).Infinite := by
    unfold U; refine Set.Infinite.image ?_ ?_
    · exact Set.injOn_of_injective (Subtype.val_injective.comp e.symm.injective)
    · exact Set.Infinite.prod_right Set.infinite_univ (Set.singleton_nonempty _)
  have hd i : Disjoint X (U i) := by
    refine Set.subset_compl_iff_disjoint_left.mp ?_
    unfold U; simp only [Set.image, Function.comp]
    rintro _ ⟨x, _, rfl⟩; exact Subtype.coe_prop _
  have hc : Cardinal.mk ↑(Y \ X) ≤ Cardinal.mk (U true) := by
    refine le_of_le_of_eq Cardinal.mk_le_aleph0 ?_
    exact (@Cardinal.mk_eq_aleph0 _ _ (hU _).to_subtype).symm
  obtain ⟨Z, hZ, e', hext⟩ :=
    Lpo.perm_extend_to (U true) (Equiv.refl X) hsub (hd true) hc
  refine ⟨X ∪ Z, e', ?_, hext⟩
  refine Set.Infinite.mono ?_ (hU false)
  refine Set.subset_compl_iff_disjoint_left.mpr (Disjoint.union_left ?_ ?_)
  · exact hd false
  · refine Disjoint.mono_left hZ ?_
    refine (Set.disjoint_image_iff ?_).mpr ?_
    · exact Subtype.val_injective.comp e.symm.injective
    · refine Set.disjoint_prod.mpr (Or.inl ?_)
      refine Set.disjoint_singleton.mpr ?_
      simp only [ne_eq, Bool.true_eq_false, not_false_eq_true]

lemma exists_extension {l : Type} [PartialOrder l] [OrderBot l] (c : Chain (Pom l)) (n : ℕ)
    (lc : LpoChain l c n) :
    ∃ lc' : LpoChain l c (n + 1), ∀ k : Fin n, lc.val k = lc'.val k.castSucc := by
  match n with
  | Nat.zero =>
    have ⟨α, heq⟩ := (c 0).exists_rep
    obtain ⟨Y, e, hY, he⟩ :=
      exists_extensible_perm Set.finite_empty.infinite_compl bot_le (Y := α.nodes)
    use {
      val := fun _ ↦ α.permute e
      property := by
        refine ⟨?_, fun n ↦ ⟨?_, ?_⟩⟩
        · intro _ _ _; exact le_refl _
        · simp only [Lpo.permute, Lpo.nodes]; exact hY
        · have := n.fin_one_eq_zero; subst this
          exact heq.symm.trans (Quotient.eq_iff_equiv.mpr ⟨e, rfl⟩)
    }
    intro n; exact Fin.elim0 n
  | Nat.succ n =>
    have hle := c.monotone' (Nat.le_succ n)
    have ⟨hinf, hc⟩ := lc.property.2 ⟨n, Nat.lt_succ_self _⟩
    have ⟨β, hβ, hle⟩ := Pom.le_lpo hinf (le_of_eq_of_le hc.symm hle)
    obtain ⟨Y, e, hY, he⟩ :=
      exists_extensible_perm hinf hle.nodes
    use {
      val := fun k ↦ if hk : k.val < n.succ then lc.val ⟨k.val, hk⟩ else β.permute e
      property := by
        refine ⟨fun i j hij ↦ ?_, fun j ↦ ⟨?_, ?_⟩⟩ <;>
          by_cases hj : j.val < n.succ <;> simp only [hj, ↓reduceDIte]
        · have hi := lt_of_le_of_lt (Fin.val_fin_le.mpr hij) hj
          rw [dif_pos hi]; exact lc.property.1 hij
        · by_cases hi : i.val < n.succ
          · rw [dif_pos hi]
            have := le_of_eq_of_le (Lpo.permute_refl _).symm (Lpo.permute_monotone hle he)
            refine (lc.property.1 ?_).trans this
            simp only [Nat.succ_eq_add_one, Fin.mk_le_mk, Nat.le_of_lt_succ hi]
          · rw [dif_neg hi]
        · exact (lc.property.2 ⟨j, hj⟩).1
        · exact hY
        · exact (lc.property.2 ⟨j, hj⟩).2
        · have := eq_of_le_of_not_lt (Nat.le_of_lt_succ j.isLt) hj; rw [this]
          exact hβ.trans (Quotient.eq_iff_equiv.mpr ⟨e, rfl⟩)
    }
    intro k; simp only [Nat.succ_eq_add_one, Fin.val_castSucc, Fin.is_lt,
      ↓reduceDIte, Fin.eta]

def empty {l : Type} [PartialOrder l] [OrderBot l] {c : Chain (Pom l)} : LpoChain l c 0 := {
  val := Fin.elim0
  property := by refine ⟨?_, ?_⟩; all_goals { intro n ; exfalso ; exact Fin.elim0 n }
}

lemma monotone {l : Type} [PartialOrder l] [OrderBot l] {c : Chain (Pom l)} {n : ℕ}
    {i j : Fin n} {lc : LpoChain l c n} (hle : i ≤ j) : lc.val i ≤ lc.val j := lc.property.1 hle

lemma mem_pom {l : Type} [PartialOrder l] [OrderBot l] {c : Chain (Pom l)} {n : ℕ}
    (i : Fin n) {lc : LpoChain l c n} : lc.val i ∈ c i := (lc.property.2 i).2

end LpoChain

lemma exists_lpo_chain_of_pom_chain {l : Type} [PartialOrder l] [OrderBot l] (c : Chain (Pom l)) :
    ∃ c' : Chain (Lpo l), ∀ i, c' i ∈ c i := by
  choose f hf using LpoChain.exists_extension c
  let ch n : LpoChain l c n := Nat.rec LpoChain.empty f n
  use {
    toFun n := (ch (n+1)).val ⟨n, Nat.lt_succ_self _⟩
    monotone' := by
      refine monotone_nat_of_le_succ ?_
      intro n; unfold ch
      refine le_of_eq_of_le (hf _ _ _) (LpoChain.monotone ?_)
      refine Fin.le_iff_val_le_val.mpr ?_
      simp only [Fin.castSucc_mk, le_add_iff_nonneg_right, zero_le]
  }
  intro n
  simp only [ch, DFunLike.coe]
  exact LpoChain.mem_pom (l := l) ⟨n, Nat.lt_succ_self _⟩

variable {l : Type} [DCPO l] [OrderBot l] [ScottCompact l]

lemma upper_bound_of_compact (c : Chain (Lpo l)) (n : ℕ) :
    ∃ i, (ωSup c).trunc n ≤ c i := by
  let X := ((ωSup c).trunc n).nodes
  have h : ∀ x : ↑X, ∃ i : ℕ,
      x.val ∈ (c i).nodes ∧ ((ωSup c).trunc n).lab x ≤ (c i).lab x := by
    intro ⟨x, hx, hlev⟩
    simp only [Lpo.ωSup_nodes, Set.mem_iUnion] at hx
    obtain ⟨i, hx⟩ := hx
    have ⟨ℓ, h, hlab⟩ :=
      ScottCompact.scottCompact ((ωSup c).lab x)
        ((Chain.to_dSet c).image _ (lab_monotone x))
        (by refine le_of_eq ?_; rfl)
    obtain ⟨β, hβ, rfl⟩ := (Set.mem_image _ _ _).mp h
    obtain ⟨j, rfl⟩ := Set.mem_range.mp hβ
    refine ⟨max i j, ?_, ?_⟩
    · exact (c.monotone' le_sup_left).nodes hx
    · exact
        ((Lpo.trunc_le _ _).lab _).trans
          (hlab.trans
            ((c.monotone' le_sup_right).lab _))
  choose f hf using h
  have hne : Nonempty ↑X := by
    obtain ⟨r, hr, hrl⟩ := (ωSup c).property.rel.single_rooted
    refine ⟨r, hr, ?_⟩; exact le_of_eq_of_le (lev_root hr hrl) bot_le
  obtain ⟨k, hk⟩ := @Finite.exists_max _ _ ((ωSup c).trunc n).property hne _ f
  refine ⟨f k, ?_⟩
  have hnodes : X ⊆ (c (f k)).nodes := by
    intro x hx; exact (c.monotone' (hk _)).nodes (hf ⟨x, hx⟩).1
  constructor
  · exact hnodes
  · intro x hx y hrel; refine (Lpo.trunc_le _ _).downcl x hx y ?_
    exact le_rel (le_ωSup _ _) hrel
  · intro x hx y hy
    exact
      ((Lpo.trunc_le _ _).rel _ hx _ hy).trans
        ((le_ωSup c _).rel _ (hnodes hx) _ (hnodes hy)).symm
  · intro x; by_cases hx : x ∈ X
    · exact (hf ⟨x, hx⟩).2.trans ((c.monotone' (hk ⟨x, hx⟩)).lab x)
    · refine le_of_eq_of_le ?_ bot_le
      exact ((ωSup c).trunc n).val.property.lab_dom _ hx
  · intro x hx;
    refine ((Lpo.trunc_le (ωSup c) n).form x hx).trans ?_
    exact ((le_ωSup c _).form _ (hnodes hx)).symm
  · intro x hx
    rcases (Lpo.trunc_le _ n).succ _ ((le_ωSup c _).nodes hx) with
        hx' | ⟨z, hbot, hrel⟩
    · left; exact hx'
    · right; refine ⟨z, hbot, ?_⟩
      refine ((le_ωSup c _).rel _ ?_ _ hx).mpr hrel
      exact (le_ωSup c _).downcl _ hx _ hrel

-- Inspired by Lemma D.4 from CONCUR'25
lemma lpo_chain_pom_chain_lub
    {cl : Chain (Lpo l)} {cp : Chain (Pom l)}
    (h : ∀ i, cl i ∈ cp i) :
    IsLUB (Set.range cp) (Pom.mk (ωSup cl)) := by
  constructor
  · intro p hp; obtain ⟨i, rfl⟩ := Set.mem_range.mpr hp
    exact ⟨cl i, h i, ωSup cl, rfl, le_ωSup _ _⟩
  · simp only [lowerBounds, upperBounds, Set.mem_range, forall_exists_index,
      forall_apply_eq_imp_iff, Set.mem_setOf_eq]; intro p hp
    refine pom_ge_iff_ge_fin ?_; intro n
    rw [Pom.trunc_mk, Pomfin.mk_to_pom]
    obtain ⟨i, hi⟩ :=  upper_bound_of_compact cl n
    refine le_trans ⟨(ωSup cl).trunc n, ?_, cl i, h i, hi⟩ (hp i)
    refine Quotient.eq_iff_equiv.mpr ?_; rfl

def lpo_chain_to_pom {l : Type} [PartialOrder l] [OrderBot l] (c : Chain (Lpo l)) :
    Chain (Pom l) := {
  toFun n := Quotient.mk _ (c n)
  monotone' i j hle := ⟨c i, rfl, c j, rfl, c.monotone' hle⟩
}
lemma lpo_chain_to_pom_lub {l : Type} [DCPO l] [OrderBot l] [ScottCompact l]
    (c : Chain (Lpo l)) :
    IsLUB (Set.range (lpo_chain_to_pom c)) (Quotient.mk _ (ωSup c)) :=
  lpo_chain_pom_chain_lub (fun _ ↦ rfl)

noncomputable instance {l : Type} [DCPO l] [OrderBot l] [ScottCompact l] :
    OmegaCompletePartialOrder (Pom l) where
  ωSup c := Quotient.mk' (ωSup (exists_lpo_chain_of_pom_chain c).choose)
  le_ωSup c i := by
    refine (lpo_chain_pom_chain_lub (exists_lpo_chain_of_pom_chain c).choose_spec).1 ?_
    exact Set.mem_range.mpr ⟨i, rfl⟩
  ωSup_le c p h := by
    refine (lpo_chain_pom_chain_lub (exists_lpo_chain_of_pom_chain c).choose_spec).2 ?_
    intro q hq; obtain ⟨i, rfl⟩ := Set.mem_range.mpr hq; exact h i
