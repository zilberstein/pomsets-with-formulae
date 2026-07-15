import Pom.Lpo.Operations.Par.Defs
import Pom.Lpo.Order

namespace Lpo

lemma par_monotone {l : Type} [PartialOrder l] [OrderBot l]
    {x : Node} {ℓ ℓ' : l} {α α' β β' : Lpo l} {φ₁ φ₂ : Form Node}
    (hx₁ : x ∉ α'.nodes) (hx₂ : x ∉ β'.nodes) (hd : Disjoint α'.nodes β'.nodes)
    (hroot : ℓ ≠ ⊥)
    (hφ₁ : Form.literal x ≤ φ₁ ∧ φ₁.DependsOn {x})
    (hφ₂ : (Form.literal x).not ≤ φ₂ ∧ φ₂.DependsOn {x})
    (hle : ℓ ≤ ℓ') (hle₁ : α ≤ α') (hle₂ : β ≤ β') :
    par_gen
      (fun h ↦ hx₁ (hle₁.nodes h))
      (fun h ↦ hx₂ (hle₂.nodes h))
      (hd.mono hle₁.nodes hle₂.nodes) hroot hφ₁ hφ₂ ≤
    par_gen hx₁ hx₂ hd (ne_bot_of_le_ne_bot hroot hle) hφ₁ hφ₂ := by
  have hd' := hd.mono hle₁.nodes hle₂.nodes
  unfold par_gen par_base; constructor
  · exact Set.insert_subset_insert (Set.union_subset_union hle₁.nodes hle₂.nodes)
  · rintro y hy z (⟨rfl, hz | hz⟩ | hz | hz) <;>
      rcases Set.eq_or_mem_of_mem_insert hy with (rfl | hy | hy) <;>
      try (exact Set.mem_insert _ _)
    · exfalso; exact hx₁ (α'.property.rel_dom hz).2
    · exact Set.mem_insert_of_mem _ (Set.mem_union_left _ (hle₁.downcl _ hy _ hz))
    · exfalso; refine Set.disjoint_left.mp hd ?_ (hle₂.nodes hy)
      exact (α'.property.rel_dom hz).2
    · exfalso; exact hx₂ (β'.property.rel_dom hz).2
    · exfalso; refine Set.disjoint_right.mp hd ?_ (hle₁.nodes hy)
      exact (β'.property.rel_dom hz).2
    · exact Set.mem_insert_of_mem _ (Set.mem_union_right _ (hle₂.downcl _ hy _ hz))
  · intro y hy z hz
    have hrel₁ {γ γ' : Lpo l} (hle : γ ≤ γ') {u v : Node}
        (h : u ∉ γ'.nodes) : γ.rel u v = γ'.rel u v := by
      ext; constructor <;> intro hc <;> exfalso
      · exact h (hle.nodes (γ.property.rel_dom hc).1)
      · exact h (γ'.property.rel_dom hc).1
    have hrel₂ {γ γ' : Lpo l} (hle : γ ≤ γ') {u v : Node}
        (h : v ∉ γ'.nodes) : γ.rel u v = γ'.rel u v := by
      ext; constructor <;> intro hc <;> exfalso
      · exact h (hle.nodes (γ.property.rel_dom hc).2)
      · exact h (γ'.property.rel_dom hc).2
    have hx₁' := (fun hx ↦ hx₁ (hle₁.nodes hx))
    have hx₂' := (fun hx ↦ hx₂ (hle₂.nodes hx))
    rcases Set.eq_or_mem_of_mem_insert hy with (rfl | hy' | hy') <;>
    rcases Set.eq_or_mem_of_mem_insert hz with (rfl | hz | hz) <;>
    refine congrArg₂ _ ?_ (congrArg₂ _ ?_ ?_) <;>
    (try ext; constructor <;> rintro ⟨rfl, _⟩ <;> exfalso <;>
        exact hx₁ (hle₁.nodes hy')) <;>
    (try ext; constructor <;> rintro ⟨rfl, _⟩ <;> exfalso <;>
        exact hx₂ (hle₂.nodes hy')) <;>
    (try refine hrel₁ hle₁ ?_; assumption) <;>
    (try refine hrel₂ hle₁ ?_; assumption) <;>
    (try refine hrel₁ hle₂ ?_; assumption) <;>
    (try refine hrel₂ hle₂ ?_; assumption)
    · refine congrArg₂ _ rfl (congrArg₂ Or ?_ ?_)
      · ext; exact ⟨fun h ↦ False.elim (hx₁ (hle₁.nodes h)),
                     fun h ↦ False.elim (hx₁ h)⟩
      · ext; exact ⟨fun h ↦ False.elim (hx₂ (hle₂.nodes h)),
                     fun h ↦ False.elim (hx₂ h)⟩
    · refine congrArg₂ _ rfl (congrArg₂ Or ?_ ?_)
      · ext; exact ⟨fun _ ↦ hle₁.nodes hz, fun _ ↦ hz⟩
      · ext; constructor
        · intro hc; exfalso
          exact Set.disjoint_left.mp hd (hle₁.nodes hz) (hle₂.nodes hc)
        · intro hc; exfalso
          exact Set.disjoint_left.mp hd (hle₁.nodes hz) hc
    · refine congrArg₂ _ rfl (congrArg₂ Or ?_ ?_) <;> ext <;> constructor <;>
        intro h
      · exact hle₁.nodes h
      · exfalso; exact Set.disjoint_left.mp hd h (hle₂.nodes hz)
      · exact hle₂.nodes h
      · exact hz
    · exact hle₁.rel _ hy' _ hz
    · exact hrel₁ hle₂ (Set.disjoint_left.mp hd (hle₁.nodes hy'))
    · exact hrel₂ hle₁ (Set.disjoint_right.mp hd (hle₂.nodes hz))
    · exact hrel₁ hle₂ (Set.disjoint_left.mp hd (hle₁.nodes hy'))
    · exact hrel₁ hle₁ (Set.disjoint_right.mp hd (hle₂.nodes hy'))
    · exact hrel₂ hle₂ (Set.disjoint_left.mp hd (hle₁.nodes hz))
    · exact hrel₁ hle₁ (Set.disjoint_right.mp hd (hle₂.nodes hy'))
    · exact hle₂.rel _ hy' _ hz
  · intro y; by_cases hx : x = y <;> simp only [lab, hx, ↓reduceIte]
    · exact hle
    · by_cases hy : y ∈ α'.val.nodes
      · conv => rhs; exact if_pos hy
        by_cases hy' : y ∈ α.val.nodes
        · conv => lhs; exact if_pos hy'
          exact hle₁.lab y
        · conv => lhs; exact if_neg hy'
          refine le_of_eq_of_le ?_ bot_le
          refine β.property.lab_dom _ fun hx ↦ Set.disjoint_left.mp hd hy (hle₂.nodes hx)
      · conv => rhs; exact if_neg hy
        have hy' : y ∉ α.val.nodes := fun hy' ↦ hy (hle₁.nodes hy')
        conv => lhs; exact if_neg hy'
        exact hle₂.lab y
  · intro y hy; rcases Set.eq_or_mem_of_mem_insert hy with (rfl | hy | hy)
    · ext v; constructor <;> (intro _; left; rfl)
    · have hx : x ≠ y := by rintro rfl; exact hx₁ (hle₁.nodes hy)
      have hy' : y ∈ α'.val.nodes := hle₁.nodes hy
      ext v; refine or_congr (Iff.refl _) (or_congr ?_ ?_)
      · refine and_congr ?_ (and_congr ?_ (Iff.refl _))
        · constructor <;> intro _ <;> assumption
        · exact congrFun (hle₁.form _ hy) _ |> iff_iff_eq.mpr
      · constructor <;> intro ⟨hc, _⟩ <;> exfalso
        · exact Set.disjoint_left.mp hd' hy hc
        · exact Set.disjoint_left.mp hd hy' hc
    · have hx : x ≠ y := by rintro rfl; exact hx₂ (hle₂.nodes hy)
      have hy' : y ∈ β'.val.nodes := hle₂.nodes hy
      ext v; refine or_congr (Iff.refl _) (or_congr ?_ ?_)
      · constructor <;> intro ⟨hc, _⟩ <;> exfalso
        · exact Set.disjoint_right.mp hd' hy hc
        · exact Set.disjoint_right.mp hd hy' hc
      · refine and_congr ?_ (and_congr ?_ (Iff.refl _))
        · constructor <;> intro _ <;> assumption
        · exact congrFun (hle₂.form _ hy) _ |> iff_iff_eq.mpr
  · intro y hy
    rcases Set.eq_or_mem_of_mem_insert hy with rfl | hmem | hmem
    · left; exact Set.mem_insert _ _
    · rcases hle₁.succ _ hmem with hy | ⟨z, hbot, hzy⟩
      · left; exact Set.mem_insert_of_mem _ (Or.inl hy)
      · right; simp only [bots, nodes, lab, Set.mem_setOf_eq]
        refine ⟨z, ⟨?_, ?_⟩, ?_⟩
        · exact Set.mem_insert_of_mem _ (Or.inl hbot.1)
        · refine (if_neg ?_).trans <| (if_pos hbot.1).trans hbot.2
          rintro rfl; apply hx₁; exact hle₁.nodes hbot.1
        · right; left; exact hzy
    · rcases hle₂.succ _ hmem with hy | ⟨z, hbot, hzy⟩
      · left; exact Set.mem_insert_of_mem _ (Or.inr hy)
      · right; simp only [bots, nodes, lab, Set.mem_setOf_eq]
        refine ⟨z, ⟨?_, ?_⟩, ?_⟩
        · exact Set.mem_insert_of_mem _ (Or.inr hbot.1)
        · refine (if_neg ?_).trans <| (if_neg ?_).trans hbot.2
          · rintro rfl; apply hx₂; exact hle₂.nodes hbot.1
          · exact Set.disjoint_right.mp hd' hbot.1
        · right; right; exact hzy

end Lpo
