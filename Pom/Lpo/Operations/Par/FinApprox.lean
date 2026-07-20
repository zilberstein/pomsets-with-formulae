import Pom.Lpo.Operations.Par.Defs
import Pom.Lpo.Order.FinApprox

namespace Lpo

variable {l : Type} [Preorder l] [OrderBot l] {x : Node} {ℓ : l} {α β : Lpo l}
    {φ₁ φ₂ : Form Node}
    {hx : x ∉ α.nodes} {hx' : x ∉ β.nodes} {hd : Disjoint α.nodes β.nodes}
    {hroot : ℓ ≠ ⊥}
    {hφ₁ : Form.literal x ≤ φ₁ ∧ φ₁.DependsOn {x}}
    {hφ₂ : (Form.literal x).not ≤ φ₂ ∧ φ₂.DependsOn {x}}
    (n : ℕ)

lemma par_lev_root :
    (par_gen hx hx' hd hroot hφ₁ hφ₂).rel.lev x = 0 :=
  (congrFun (par_lev hx hx' hd) _).trans <| if_pos rfl

lemma par_lev_left {z : Node} (hz : z ∈ α.nodes) :
    (par_gen hx hx' hd hroot hφ₁ hφ₂).rel.lev z = α.rel.lev z + 1 := by
  refine (congrFun (par_lev hx hx' hd) _).trans <| (if_neg ?_).trans <| if_pos hz
  rintro rfl; exact hx hz

lemma par_lev_right {z : Node} (hz : z ∈ β.nodes) :
    (par_gen hx hx' hd hroot hφ₁ hφ₂).rel.lev z = β.rel.lev z + 1 := by
  refine (congrFun (par_lev hx hx' hd) _).trans <| ?_
  refine (if_neg ?_).trans <| (if_neg ?_).trans <| if_pos hz
  · rintro rfl; exact hx' hz
  · exact Set.disjoint_right.mp hd hz

lemma par_lev_left_le {z : Node} (hz : z ∈ α.nodes) :
    (par_gen hx hx' hd hroot hφ₁ hφ₂).rel.lev z ≤ n + 1 ↔ α.rel.lev z ≤ n := by
  conv => lhs; lhs; exact par_lev_left hz
  exact ENat.add_le_add_iff_right (ENat.one_ne_top)

lemma par_lev_right_le {z : Node} (hz : z ∈ β.nodes) :
    (par_gen hx hx' hd hroot hφ₁ hφ₂).rel.lev z ≤ n + 1 ↔ β.rel.lev z ≤ n := by
  conv => lhs; lhs; exact par_lev_right hz
  exact ENat.add_le_add_iff_right (ENat.one_ne_top)

lemma par_trunc_nodes :
    ((par_gen hx hx' hd hroot hφ₁ hφ₂).trunc (n + 1)).nodes =
    (par_gen
      (fun h ↦ hx <| (α.trunc_le n).nodes h)
      (fun h ↦ hx' <| (β.trunc_le n).nodes h)
      (hd.mono (α.trunc_le n).nodes (β.trunc_le n).nodes)
      hroot hφ₁ hφ₂).nodes := by
  ext z; constructor
  · rintro ⟨rfl | hz | hz, hlev⟩
    · exact Set.mem_insert _ _
    · right; left; refine ⟨hz, ?_⟩; exact (par_lev_left_le _ hz).mp hlev
    · right; right; refine ⟨hz, ?_⟩; exact (par_lev_right_le _ hz).mp hlev
  · rintro (rfl | ⟨hz, hlev⟩ | ⟨hz, hlev⟩)
    · refine ⟨Set.mem_insert _ _, ?_⟩; exact le_of_eq_of_le par_lev_root bot_le
    · refine ⟨Or.inr <| Or.inl hz, ?_⟩
      exact (par_lev_left_le _ hz).mpr hlev
    · refine ⟨Or.inr <| Or.inr hz, ?_⟩
      exact (par_lev_right_le _ hz).mpr hlev

lemma par_trunc_rel :
    ((par_gen hx hx' hd hroot hφ₁ hφ₂).trunc (n + 1)).rel =
    (par_gen
      (fun h ↦ hx <| (α.trunc_le n).nodes h)
      (fun h ↦ hx' <| (β.trunc_le n).nodes h)
      (hd.mono (α.trunc_le n).nodes (β.trunc_le n).nodes)
      hroot hφ₁ hφ₂).rel := by
  ext i j;
  by_cases hlev :
      (par_gen hx hx' hd hroot hφ₁ hφ₂).rel.lev i ≤ n + 1 ∧
      (par_gen hx hx' hd hroot hφ₁ hφ₂).rel.lev j ≤ n + 1
  · refine Iff.trans (and_iff_left hlev) <| ?_
    have ⟨hli, hlj⟩ := hlev
    refine or_congr ?_ (or_congr ?_ ?_)
    · refine and_congr_right ?_; rintro rfl; refine or_congr ?_ ?_ <;>
        refine ⟨fun h ↦ ⟨h, ?_⟩, And.left⟩
      · exact (par_lev_left_le _ h).mp hlj
      · exact (par_lev_right_le _ h).mp hlj
    · refine ⟨fun hrel ↦ ⟨hrel, ?_⟩, And.left⟩
      have ⟨hi, hj⟩ := α.property.rel_dom hrel
      exact ⟨(par_lev_left_le _ hi).mp hli, (par_lev_left_le _ hj).mp hlj⟩
    · refine ⟨fun hrel ↦ ⟨hrel, ?_⟩, And.left⟩
      have ⟨hi, hj⟩ := β.property.rel_dom hrel
      exact ⟨(par_lev_right_le _ hi).mp hli, (par_lev_right_le _ hj).mp hlj⟩
  · constructor
    · intro ⟨_, hc⟩; contradiction
    · rintro (⟨rfl, hj⟩ | ⟨hrel, hli, hlj⟩ | ⟨hrel, hli, hlj⟩) <;>
        exfalso <;> refine not_and.mp hlev ?_ ?_
      · exact le_of_eq_of_le par_lev_root bot_le
      · rcases hj with ⟨hj, hjl⟩ | ⟨hj, hjl⟩
        · exact (par_lev_left_le _ hj).mpr hjl
        · exact (par_lev_right_le _ hj).mpr hjl
      all_goals {
        have ⟨hi, hj⟩ := (Subtype.property (_ : Lpo l)).rel_dom hrel
        try refine (par_lev_left_le _ ?_).mpr ?_ <;> assumption
        try refine (par_lev_right_le _ ?_).mpr ?_ <;> assumption
      }

open Classical in
lemma par_trunc_lab :
    ((par_gen hx hx' hd hroot hφ₁ hφ₂).trunc (n + 1)).lab =
    (par_gen
      (fun h ↦ hx <| (α.trunc_le n).nodes h)
      (fun h ↦ hx' <| (β.trunc_le n).nodes h)
      (hd.mono (α.trunc_le n).nodes (β.trunc_le n).nodes)
      hroot hφ₁ hφ₂).lab := by
  ext z
  by_cases hzl : (par_gen hx hx' hd hroot hφ₁ hφ₂).rel.lev z < n + 1
  · conv => lhs; exact if_pos hzl
    have h := ENat.lt_coe_add_one_iff.mp hzl
    refine ite_congr rfl (fun _ ↦ rfl) (fun hne ↦ ite_congr ?_ ?_ ?_)
    · ext; refine ⟨fun hz ↦ ⟨hz, ?_⟩, And.left⟩
      refine (par_lev_left_le _ hz).mp (le_of_lt hzl)
    · intro ⟨hz, _⟩; symm; refine if_pos ?_
      refine (ENat.add_lt_add_iff_right (ENat.one_ne_top)).mp ?_
      exact lt_of_eq_of_lt (par_lev_left hz).symm hzl
    · intro _; symm
      by_cases hz : z ∈ β.nodes
      · refine if_pos ?_
        refine (ENat.add_lt_add_iff_right (ENat.one_ne_top)).mp ?_
        exact lt_of_eq_of_lt (par_lev_right hz).symm hzl
      · conv => rhs; exact β.property.lab_dom _ hz
        by_cases hz' : β.rel.lev z < n
        · exact (if_pos hz').trans <| β.property.lab_dom _ hz
        · exact if_neg hz'
  · conv => lhs; exact if_neg hzl
    rcases not_lt.mp hzl |> lt_or_eq_of_le with hgt | heq
    · symm; refine (par_gen _ _ _ _ _ _).property.lab_dom _ ?_
      rintro (rfl | ⟨hz, hlev⟩ | ⟨hz, hlev⟩) <;> apply not_le_of_gt hgt
      · exact le_of_eq_of_le par_lev_root bot_le
      · exact (par_lev_left_le _ hz).mpr hlev
      · exact (par_lev_right_le _ hz).mpr hlev
    · symm; refine (if_neg ?_).trans <| (ite_congr rfl ?_ ?_).trans <| ite_self ⊥
      · rintro rfl; apply hzl; rw [par_lev_root]; exact Nat.cast_add_one_pos n
      · intro ⟨hz, _⟩; refine if_neg ?_; intro hc; apply hzl
        rw [par_lev_left hz]; exact (ENat.add_lt_add_iff_right (ENat.one_ne_top)).mpr hc
      · intro _; refine (ite_congr rfl ?_ (fun _ ↦ rfl)).trans <| ite_self ⊥
        intro hlev; refine β.property.lab_dom _ ?_
        intro hz; rw [par_lev_right hz] at heq
        apply (add_left_inj_of_ne_top (ENat.one_ne_top)).mp at heq;
        rw [← heq] at hlev; exact lt_irrefl _ hlev

lemma par_trunc_form :
    ((par_gen hx hx' hd hroot hφ₁ hφ₂).trunc (n + 1)).form =
    (par_gen
      (fun h ↦ hx <| (α.trunc_le n).nodes h)
      (fun h ↦ hx' <| (β.trunc_le n).nodes h)
      (hd.mono (α.trunc_le n).nodes (β.trunc_le n).nodes)
      hroot hφ₁ hφ₂).form := by
  ext z v; by_cases hlev : (par_gen hx hx' hd hroot hφ₁ hφ₂).rel.lev z ≤ n + 1
  · conv => lhs; exact congrFun (if_pos hlev) _
    refine or_congr (Iff.refl _) (or_congr ?_ ?_)
    · constructor
      · intro ⟨hz, hform, hφ⟩; apply (par_lev_left_le _ hz).mp at hlev
        refine ⟨⟨hz, hlev⟩, ?_, hφ⟩; exact (congrFun (if_pos hlev) _).mpr hform
      · intro ⟨⟨hz, hlev⟩, hform, hφ⟩; refine ⟨hz, ?_, hφ⟩
        exact (congrFun (if_pos hlev) _).mp hform
    · constructor
      · intro ⟨hz, hform, hφ⟩; apply (par_lev_right_le _ hz).mp at hlev
        refine ⟨⟨hz, hlev⟩, ?_, hφ⟩; exact (congrFun (if_pos hlev) _).mpr hform
      · intro ⟨⟨hz, hlev⟩, hform, hφ⟩; refine ⟨hz, ?_, hφ⟩
        exact (congrFun (if_pos hlev) _).mp hform
  · constructor
    · intro hc; exfalso; exact (congrFun (if_neg hlev) _).mp hc
    · rintro (rfl | ⟨⟨hz, hlev'⟩, _⟩ | ⟨⟨hz, hlev'⟩, _⟩) <;> exfalso <;> apply hlev
      · exact le_of_eq_of_le par_lev_root bot_le
      · exact (par_lev_left_le _ hz).mpr hlev'
      · exact (par_lev_right_le _ hz).mpr hlev'

lemma par_trunc :
    (par_gen hx hx' hd hroot hφ₁ hφ₂).trunc (n + 1) =
    par_gen
      (fun h ↦ hx <| (α.trunc_le n).nodes h)
      (fun h ↦ hx' <| (β.trunc_le n).nodes h)
      (hd.mono (α.trunc_le n).nodes (β.trunc_le n).nodes)
      hroot hφ₁ hφ₂ := by
  ext1
  · exact par_trunc_nodes n
  · exact par_trunc_rel n
  · exact par_trunc_lab n
  · exact par_trunc_form n

end Lpo
