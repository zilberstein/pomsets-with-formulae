import Pom.Lpo.Operations.Seq

namespace Lpofin

variable {l : Type} [PartialOrder l] [OrderBot l]

lemma branches_permute {α α' : Lpofin l} {e : α.nodes ≃ α'.nodes}
    (h : α.permute e = α') :
    ∀ φ ∈ α.branches, φ.permute e ∈ α'.branches := by
  rintro φ ⟨s, ⟨hne, hsub, ⟨v, hsat⟩, hstk, hmax⟩, rfl⟩
  let t := Set.range
    (fun x : ↑s ↦ (e ⟨x.val, (hsub x.property).1⟩).val)
  refine ⟨t, ⟨?_, ?_, ?_, ?_, ?_⟩, ?_⟩ <;> subst t
  · exact @Set.range_nonempty _ _ hne.coe_sort _
  · conv => rhs; rw [← h]
    intro x hx; obtain ⟨⟨y, hy⟩, _, rfl⟩ := hx
    constructor
    · exact Subtype.coe_prop _
    · intro hc
      have ⟨hy', h'⟩ := hsub hy; apply h'
      intro v hform
      have ⟨⟨z, hz, hbot⟩, _, hform'⟩ :=
        hc (Form.image v e) ((Lpo.permute_form_sat_iff hy').mp hform)
      refine ⟨⟨(e.symm ⟨_, hz⟩).val, Subtype.coe_prop _, ?_⟩, ?_⟩
      · refine Eq.trans ?_ hbot; exact (if_pos hz).symm
      · refine (Lpo.permute_form_sat_iff (Subtype.coe_prop _) (e := e)).mpr ?_
        conv => arg 2; arg 1; exact e.apply_symm_apply _
        exact ⟨hz, hform'⟩
  · use Form.image v e; rintro ⟨x, ⟨⟨y, hy⟩, _, rfl⟩⟩
    conv => simp only; arg 1; exact h.symm
    refine (Lpo.permute_form_sat_iff _).mp (hsat ⟨_, hy⟩)
  · intro v hv ⟨⟨z, hz, hbot⟩, hform⟩
    refine hstk (Form.image v e.symm) ?_ ?_
    · intro ⟨x, hx⟩; refine ((Lpo.permute_form_sat_iff ?_ (e := e)).mpr ?_)
      · exact (hsub hx).1
      · conv => arg 3; arg 2; exact e.symm_symm.symm
        conv => arg 3; exact Form.image_inv v e.symm
        refine Lpo.form_inter_nodes_sat_iff.mp ?_
        conv at hv => arg 1; exact h.symm
        refine hv ⟨(e ⟨x, _⟩).val, ?_⟩
        refine Set.mem_range.mpr ⟨⟨x, hx⟩, rfl⟩
    · refine ⟨⟨(e.symm ⟨z, hz⟩).val, Subtype.coe_prop _, ?_⟩, ?_⟩
      · rw [← h] at hbot; simp only [Lpo.lab, permute, Lpo.permute, dite_eq_right_iff] at hbot
        exact hbot hz
      · simp only
        refine (Lpo.permute_form_sat_iff (Subtype.coe_prop _) (e := e)).mpr ?_
        conv => arg 3; exact Form.image_inv v e.symm
        refine Lpo.form_inter_nodes_sat_iff.mp ?_
        conv => arg 2; simp only [Subtype.coe_eta]; arg 1; exact e.apply_symm_apply _
        conv at hform => simp only; arg 1; exact h.symm
        exact hform
  · intro t ⟨hst, hnts⟩ hex ⟨v, hform⟩
    refine hmax (Set.range fun y : ↑t ↦ (e.symm ⟨y.val, ?_⟩).val) ?_ ?_ ?_
    · exact (hex y.property).1
    · constructor
      · intro x hx; refine Set.mem_range.mpr ⟨⟨e ⟨x, ?_⟩, ?_⟩, ?_⟩
        · exact (hsub hx).1
        · exact hst ⟨⟨x, hx⟩, rfl⟩
        · simp only [Subtype.coe_eta, Equiv.symm_apply_apply]
      · intro hc; apply hnts; intro x hx
        refine ⟨⟨(e.symm ⟨x, ?_⟩).val, ?_⟩, ?_⟩
        · exact (hex hx).1
        · exact hc ⟨⟨x, hx⟩, rfl⟩
        · simp only [Subtype.coe_eta, Equiv.apply_symm_apply]
    · rintro x ⟨y, rfl⟩; constructor
      · exact Subtype.coe_prop _
      · intro hc; apply (hex y.property).2; intro v hform
        rw [← h] at hform; simp only [Lpofin.permute, form, Lpo.permute, Lpo.form] at hform
        have ⟨hy, hform⟩ := hform
        have ⟨⟨z, hz, hbot⟩, hform⟩ := hc _ hform
        refine ⟨⟨(e ⟨_, hz⟩).val, Subtype.coe_prop _, ?_⟩, ?_⟩
        · conv => arg 1; arg 1; arg 1; exact h.symm
          simp only [Lpofin.permute, Lpo.permute, Lpo.lab]
          refine (dif_pos (Subtype.coe_prop _)).trans ?_
          conv => lhs; arg 2; simp only [Subtype.coe_eta]; arg 1; exact e.symm_apply_apply _
          exact hbot
        · simp only [← h]
          refine Lpo.form_inter_nodes_sat_iff.mpr ?_
          conv => arg 3; exact (Form.image_inv _ e.symm).symm
          conv => arg 3; arg 2; exact e.symm_symm
          exact (Lpo.permute_form_sat_iff _).mp hform
    · refine ⟨Form.image v e.symm, ?_⟩; rintro x ⟨y, _, rfl⟩
      refine (Lpo.permute_form_sat_iff (Subtype.coe_prop _) (e := e)).mpr ?_
      conv => arg 2; simp only [Subtype.coe_eta]; arg 1; exact e.apply_symm_apply _
      conv => arg 3; exact Form.image_inv _ _
      refine Lpo.form_inter_nodes_sat_iff.mp ?_
      have := hform _ y.property; rw [← h] at this; exact this
  · conv => lhs; arg 1; rw [← h]
    simp only [conj]; unfold Form.permute; ext v; constructor
    · intro hform x
      have :=
        hform ⟨(e ⟨x.val, (hsub x.property).1⟩).val, ⟨x, rfl⟩⟩
      simp only [form, Lpo.form, permute, Lpo.permute, Form.permute, Subtype.coe_eta,
        Subtype.coe_prop, exists_const] at this
      conv at this => arg 2; arg 1; exact Equiv.symm_apply_apply _ _
      exact this
    · intro hform x; have ⟨y, heq⟩ := x.property; rw [← heq]
      refine ⟨Subtype.coe_prop _, ?_⟩
      simp only [Subtype.coe_eta]
      conv => arg 1; arg 2; arg 1; exact Equiv.symm_apply_apply _ _
      exact hform y

def branches_equiv {α α' : Lpofin l} {e : α.nodes ≃ α'.nodes}
    (h : α.permute e = α') :
    α.branches ≃ α'.branches := {
  toFun φ := ⟨φ.val.permute e, branches_permute h _ φ.property⟩
  invFun φ := ⟨φ.val.permute e.symm, by {
    refine branches_permute ?_ _ φ.property
    refine Subtype.ext ?_; symm; refine (Lpo.permute_symm ?_)
    conv => rhs; arg 1; exact h.symm
    rfl
  }⟩
  left_inv := by
    rintro ⟨φ, ⟨s, ⟨_, hsub, _⟩, rfl⟩⟩
    have h (x : ↑s) := (α.val.property.form _ (hsub x.property).1).1
    ext1; ext1 v; refine Form.DependsOn.sAnd h _ _ ?_
    refine Set.disjoint_left.mpr ?_; intro x hx hx'
    have ⟨y, hrel⟩ := Set.mem_iUnion.mp hx'
    rcases Set.mem_symmDiff.mp hx with ⟨⟨z, rfl, w, heq, hw⟩, hv⟩ | ⟨hv, h⟩
    · apply hv; rw [← Subtype.val_injective heq]
      simpa only [Equiv.symm_symm, Equiv.symm_apply_apply]
    · have hx := (α.val.property.rel_dom hrel).1
      refine h ⟨e ⟨x, hx⟩, ?_, ⟨x, hx⟩, rfl, hv⟩
      simp only [Equiv.symm_apply_apply]
  right_inv := by
    rintro ⟨φ, ⟨s, ⟨_, hsub, _⟩, rfl⟩⟩
    ext1; ext1 v
    have h (x : ↑s) := (α'.val.property.form _ (hsub x.property).1).1
    refine Form.DependsOn.sAnd h _ _ ?_
    refine Set.disjoint_left.mpr ?_; intro x hx hx'
    have ⟨y, hrel⟩ := Set.mem_iUnion.mp hx'
    rcases Set.mem_symmDiff.mp hx with ⟨⟨z, rfl, y, heq, h⟩, h'⟩ | ⟨hv, h⟩
    · apply h'; rw [e.symm_symm, ← Subtype.ext heq, e.apply_symm_apply]; exact h
    · apply h; have hx := (α'.val.property.rel_dom hrel).1
      refine ⟨e.symm ⟨x, hx⟩, ?_, ?_⟩
      · rw [e.symm_symm, e.apply_symm_apply]
      · refine ⟨⟨_, hx⟩, rfl, hv⟩}

lemma form_imp_permute {l : Type} [Bot l]
    {a : Lpofin l} {Y : Set Node} {e : a.nodes ≃ Y} {φ : Form Node} {x : Node}
    (hx : x ∈ a.nodes) (hφ : φ.DependsOn a.nodes) :
    φ ≤ a.form x ↔ φ.permute e ≤ (a.permute e).form (e ⟨x, hx⟩).val := by
  classical
  constructor
  · intro himp v h
    apply Lpo.form_inter_nodes_sat_iff.mpr;
    conv in v ∩ _ => exact (Form.image_inv _ e.symm).symm
    rw [e.symm_symm]; exact (Lpo.permute_form_sat_iff _).mp (himp _ h)
  · intro himp v h
    apply (Lpo.permute_form_sat_iff hx (e := e)).mpr
    refine himp _ ?_; unfold Form.permute; conv => arg 1; exact Form.image_inv v e
    refine (hφ _ _ ?_).mp h; apply Set.disjoint_left.mpr fun y hy hy' ↦ ?_
    rcases Set.mem_symmDiff.mp hy with ⟨hv, hv'⟩ | ⟨hv, hv'⟩
    · exact hv' ⟨hv, hy'⟩
    · exact hv' hv.1

lemma branch_depends_on {α : Lpofin l} {φ : Form Node} (h : φ ∈ α.branches) :
    φ.DependsOn α.nodes := by
  obtain ⟨s, ⟨hne, hsub, _⟩, rfl⟩ := h
  refine
    Form.DependsOn.monotone _ ?_
      (Form.DependsOn.sAnd
        fun x ↦ α.val.property.form _ (hsub x.property |>.1) |>.1)
  rintro x ⟨s, ⟨y, rfl⟩, h⟩
  exact α.val.property.rel_dom h |>.1

lemma seq_isomorphic {α α' β β' : Lpofin l} {f : CopyFn α β} {g : CopyFn α' β'}
    (hα : α ≈ α') (hβ : β ≈ β') : seq α β f ≈ seq α' β' g := by
  have ⟨e, he⟩ := hα
  let eb := branches_equiv (Subtype.ext he)
  have (φ : ↑α.branches) :
      ∃ e : ((f φ).nodes ≃ (g (eb φ)).nodes), (f φ).permute e = (g (eb φ)) := by
    have ⟨ef, hf⟩ := (f.property φ).1
    have ⟨eg, hg⟩ := (g.property (eb φ)).1
    have ⟨eβ, h⟩ := hβ
    refine ⟨ef.trans (eβ.trans eg.symm), ?_⟩
    unfold Lpofin.permute; refine Subtype.ext ?_; simp only
    refine Lpo.permute_trans.symm.trans ?_
    refine Lpo.permute_trans.symm.trans ?_
    symm; refine Lpo.permute_symm (hg.trans (h.symm.trans ?_))
    refine Lpo.permute_congr _ _ hf.symm ?_
    intro x; rfl
  choose eφ h using this
  let e' := Equiv.iUnion
    (fun φ ↦ (f.property φ).2.2)
    (fun φ ↦ (g.property φ).2.2)
    eb eφ
  refine ⟨Equiv.union e e' ?_ ?_ , ?_⟩
  · refine Set.disjoint_left.mpr ?_; intro x hx hx'
    have ⟨φ, hx'⟩ := Set.mem_iUnion.mp hx'
    exact Set.disjoint_left.mp (f.property φ).2.1 hx hx'
  · refine Set.disjoint_left.mpr ?_; intro x hx hx'
    have ⟨φ, hx'⟩ := Set.mem_iUnion.mp hx'
    exact Set.disjoint_left.mp (g.property φ).2.1 hx hx'
  · ext1
    · rfl
    · ext x y
      by_cases hx : x ∈ (α'.seq β' g).nodes
      · by_cases hy : y ∈ (α'.seq β' g).nodes
        · simp only [seq, seq_base, Lpo.permute, Lpo.nodes, Lpo.rel]
          unfold Rel.permute
          refine Iff.trans ⟨fun h ↦ h.2.2, fun h ↦ ⟨hx, hy, h⟩⟩ ?_
          refine or_congr ?_ ?_
          · unfold Lpofin.rel; rw [← he]
            simp only [Lpo.permute, Lpo.rel, Rel.permute]
            constructor
            · intro hrel; have ⟨hx', hy'⟩ := (α.val.property.rel_dom hrel)
              have hx := Equiv.mem_union_symm_left hx'
              have hy := Equiv.mem_union_symm_left hy'
              refine ⟨hx, hy, ?_⟩
              rw [Equiv.union_symm_apply_left hx, Equiv.union_symm_apply_left hy] at hrel
              exact hrel
            · intro ⟨hx', hy', hrel⟩
              refine (congrArg₂ α.rel ?_ ?_).mpr hrel
              · exact Equiv.union_symm_apply_left hx'
              · exact Equiv.union_symm_apply_left hy'
          · refine eb.exists_congr ?_; intro φ
            rw [← h φ]
            simp only [Lpofin.permute, Lpo.permute, rel, Lpo.rel, nodes, Lpo.nodes, Rel.permute]
            refine or_congr ?_ ?_
            · constructor
              · intro hrel
                have ⟨hx', hy'⟩ := (f φ).val.property.rel_dom hrel
                have hx'' := Equiv.mem_union_symm_right (Set.mem_iUnion.mpr ⟨_, hx'⟩)
                have hy'' := Equiv.mem_union_symm_right (Set.mem_iUnion.mpr ⟨_, hy'⟩)
                conv at hx' => arg 2; exact Equiv.union_symm_apply_right hx''
                conv at hy' => arg 2; exact Equiv.union_symm_apply_right hy''
                unfold e' at hx'
                have hx := Equiv.mem_iUnion_symm (e := eb) hx'
                have hy := Equiv.mem_iUnion_symm (e := eb) hy'
                refine ⟨hx, hy, (congrArg₂ _ ?_ ?_).mp hrel⟩; all_goals {
                  refine (Equiv.union_symm_apply_right ?_).trans ?_
                  · assumption
                  · exact Equiv.iUnion_symm_apply' _
                }
              · intro ⟨hx', hy', hrel⟩
                refine (congrArg₂ _ ?_ ?_).mpr hrel; all_goals {
                  refine (Equiv.union_symm_apply_right ?_).trans ?_
                  · refine Set.mem_iUnion.mpr ⟨eb φ, ?_⟩; assumption
                  · exact Equiv.iUnion_symm_apply' _
                }
            · refine and_congr ?_ ?_
              · rcases hx with hx | hx
                · conv => lhs; rhs; arg 2; exact Equiv.union_symm_apply_left hx
                  refine (form_imp_permute (e := e) ?_ ?_).trans ?_
                  · exact Subtype.coe_prop _
                  · exact branch_depends_on φ.property
                  · refine forall_congr' fun v ↦ imp_congr ?_ ?_
                    · exact Iff.refl _
                    · conv => lhs; arg 2; arg 1; exact e.apply_symm_apply _
                      unfold form; conv => rhs; arg 1; exact he.symm
                      exact Iff.refl _
                · conv => lhs; rhs; arg 2; exact Equiv.union_symm_apply_right hx
                  obtain ⟨_, ⟨ψ, rfl⟩, hx⟩ := hx
                  conv => lhs; rhs; arg 2; exact Equiv.iUnion_symm_apply hx (e := eb)
                  constructor
                  · intro himp v h; exfalso
                    have := (α.val.property.form_dom _).mp ⟨_, himp _ h⟩
                    refine Set.disjoint_right.mp (f.property (eb.symm ψ)).2.1 ?_ this
                    exact Subtype.coe_prop _
                  · intro himp v h; exfalso
                    refine Set.disjoint_right.mp (g.property ψ).2.1 hx ?_
                    refine (α'.val.property.form_dom _).mp ⟨Form.image v e, himp _ ?_⟩
                    simp only [branches_equiv, Equiv.coe_fn_mk, Form.permute, eb]
                    conv => arg 2; exact Form.image_inv v e
                    refine (branch_depends_on φ.property _ _ ?_).mp h
                    apply Set.disjoint_left.mpr fun y hy hy' ↦ ?_
                    rcases Set.mem_symmDiff.mp hy with ⟨hv, hv'⟩ | ⟨hv, hv'⟩
                    · exact hv' ⟨hv, hy'⟩
                    · exact hv' hv.1
              · constructor
                · intro h;
                  have := Set.subset_iUnion (fun φ ↦ (f φ).nodes) φ h
                  rw [Equiv.union_symm] at this
                  have := Equiv.mem_union_right this
                  conv at h => arg 2; exact Equiv.union_symm_apply_right this
                  exact Equiv.mem_iUnion_symm h (e := eb)
                · intro hy
                  have := Set.subset_iUnion (fun ψ ↦ (g ψ).nodes) (eb φ) hy
                  conv => rhs; exact Equiv.union_symm_apply_right this
                  conv => rhs; exact Equiv.iUnion_symm_apply hy (e := eb)
                  sorry
        · constructor
          · intro ⟨_, hy', _⟩; exfalso; exact hy hy'
          · intro hrel; exfalso; exact hy ((seq _ _ _).val.property.rel_dom hrel).2
      · constructor
        · intro ⟨hx', _⟩; exfalso; exact hx hx'
        · intro hrel; exfalso; exact hx ((seq _ _ _).val.property.rel_dom hrel).1
    · ext x; by_cases hx : x ∈ (α'.seq β' g).nodes
      · conv => lhs; exact dif_pos hx
        classical refine dite_congr ?_ ?_ ?_
        · sorry
        · sorry
        · sorry
      · conv => lhs; exact dif_neg hx
        symm; exact (α'.seq β' g).val.property.lab_dom _ hx
    · sorry

end Lpofin
