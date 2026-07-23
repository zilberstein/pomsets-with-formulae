import Pom.Lpo.Operations.Seq
import Pom.Linearization

open Linearization

/-- If `p` depends only on `s`, `q` only on `u`, these are disjoint and `q` is satisfiable,
then conjoining `q` does not change the satisfiability of `p`. -/
lemma sat_and_indep {α : Type} {p q : Form α} {s u : Set α}
    (hp : p.DependsOn s) (hq : q.DependsOn u) (hd : Disjoint s u) (hqsat : q.sat) :
    Form.sat (p.and q) ↔ Form.sat p := by
  constructor
  · rintro ⟨v, hv⟩; exact ⟨v, hv.1⟩
  · rintro ⟨v, hv⟩
    obtain ⟨w, hw⟩ := hqsat
    have hsd1 : Disjoint (symmDiff v ((v \ u) ∪ (w ∩ u))) s := by
      rw [Set.disjoint_left]; intro x hx hxs
      have hxu : x ∉ u := fun hxu => Set.disjoint_left.mp hd hxs hxu
      rcases Set.mem_symmDiff.mp hx with ⟨hxv, hxv'⟩ | ⟨hxv', hxv⟩
      · exact hxv' (Or.inl ⟨hxv, hxu⟩)
      · rcases hxv' with ⟨hxvv, _⟩ | ⟨_, hxuu⟩
        · exact hxv hxvv
        · exact hxu hxuu
    have hsd2 : Disjoint (symmDiff w ((v \ u) ∪ (w ∩ u))) u := by
      rw [Set.disjoint_left]; intro x hx hxu
      rcases Set.mem_symmDiff.mp hx with ⟨hxw, hxv'⟩ | ⟨hxv', hxw⟩
      · exact hxv' (Or.inr ⟨hxw, hxu⟩)
      · rcases hxv' with ⟨_, hxuu⟩ | ⟨hxww, _⟩
        · exact hxuu hxu
        · exact hxw hxww
    refine ⟨(v \ u) ∪ (w ∩ u), (hp v _ hsd1) ▸ hv, (hq w _ hsd2) ▸ hw⟩

/-- The obvious equivalence between the coercions of two equal finsets. -/
def finsetCongrEq {α : Type} {s t : Finset α} (h : s = t) : s ≃ t where
  toFun x := ⟨x.val, h ▸ x.property⟩
  invFun y := ⟨y.val, h.symm ▸ y.property⟩
  left_inv _ := rfl
  right_inv _ := rfl

namespace Lpofin

variable {l : Type} [PartialOrder l] [OrderBot l]
/-- A branch formula is satisfiable. -/
lemma branch_sat (α : Lpofin l) {φ : Form Node} (hφ : φ ∈ α.branches) : φ.sat := by
  obtain ⟨S, ⟨_, _, hsat, _, _⟩, rfl⟩ := (Set.Finite.mem_toFinset _).mp hφ; exact hsat
/-- A branch formula depends only on the nodes of `α`. -/
lemma branch_dependsOn (α : Lpofin l) {φ : Form Node} (hφ : φ ∈ α.branches) :
    φ.DependsOn α.nodes := by
  obtain ⟨S, ⟨_, hsub, _, _, _⟩, rfl⟩ := (Set.Finite.mem_toFinset _).mp hφ
  unfold Lpofin.conj
  refine Form.DependsOn.monotone _ ?_ (Form.DependsOn.sAnd (s := fun _ : S ↦ α.nodes)
    (fun x => ?_))
  · exact Set.iUnion_subset fun _ => le_refl _
  · have hx : x.val ∈ α.nodes := extens_subset_nodes _ (hsub x.property)
    refine Form.DependsOn.monotone _ ?_ (α.val.property.form x.val hx).1
    intro y hy; exact (α.val.property.rel_dom hy).1

/-! ### Structural facts about `seq α β f`. -/
/-- On the nodes of `α`, `seq α β f` has the same formula as `α`. -/
lemma seq_form_alpha (α β : Lpofin l) (f : CopyFn α β) {x : Node} (hx : x ∈ α.nodes) :
    (seq α β f).form x = α.form x := by
  simp only [seq, form, Lpo.form, seq_base, if_pos hx]

/-- On the nodes of `α`, `seq α β f` has the same label as `α`. -/
lemma seq_lab_alpha (α β : Lpofin l) (f : CopyFn α β) {x : Node} (hx : x ∈ α.nodes) :
    (seq α β f).lab x = α.lab x := by
  have hf : ¬ ∃ φ : α.branches, x ∈ (f φ).nodes := by
    rintro ⟨φ, hφ⟩; exact Set.disjoint_left.mp (f.property φ).2.1 hx hφ
  simp only [seq, lab, Lpo.lab, seq_base, dif_neg hf]

/-- On the nodes of a copy `f φ`, the `seq` formula is the copy formula conjoined with the
branch condition `φ`. -/
lemma seq_form_copy (α β : Lpofin l) (f : CopyFn α β) (φ : α.branches) {z : Node}
    (hz : z ∈ (f φ).nodes) :
    (seq α β f).form z = ((f φ).form z).and φ.val := by
  have hz' : z ∉ α.nodes := Set.disjoint_right.mp (f.property φ).2.1 hz
  simp only [seq, form, Lpo.form, seq_base, if_neg hz']
  ext v; constructor
  · rintro ⟨ψ, hψ, hφv⟩
    have : φ = ψ := by
      by_contra hc
      exact Set.disjoint_left.mp ((f.property φ).2.2 ψ hc) hz
        (((f ψ).val.property.form_dom z).mp ⟨v, hψ⟩)
    subst this; exact ⟨hψ, hφv⟩
  · rintro ⟨h1, h2⟩; exact ⟨φ, h1, h2⟩

/-- On the nodes of a copy `f φ`, the `seq` label agrees with the copy label. -/
lemma seq_lab_copy (α β : Lpofin l) (f : CopyFn α β) (φ : α.branches) {z : Node}
    (hz : z ∈ (f φ).nodes) :
    (seq α β f).lab z = (f φ).lab z := by
  have hex : ∃ ψ : α.branches, z ∈ (f ψ).nodes := ⟨φ, hz⟩
  simp only [seq, lab, Lpo.lab, seq_base, dif_pos hex]
  have hchoose : hex.choose = φ := by
    by_contra hc
    exact Set.disjoint_left.mp ((f.property hex.choose).2.2 φ hc) hex.choose_spec hz
  rw [hchoose]

/-! ### The copy phase: once the remaining set lies inside a single copy `f φ`,
`seq α β f` linearizes exactly like that copy. -/
/-- Within a copy, `seq`'s minimal elements coincide with the copy's. -/
lemma seq_next_copy (α β : Lpofin l) (f : CopyFn α β) (φ : α.branches)
    (w : Finset Node) (hw : ↑w ⊆ (f φ).nodes) :
    (seq α β f).next w = (f φ).next w := by
  classical
  ext y
  simp only [next, Finset.mem_filter, Lpofin.nodes_finset, Set.Finite.mem_toFinset,
    Lpo.nodes, Lpofin.rel, Lpo.rel]
  constructor
  · rintro ⟨_, hyw, hmin⟩
    exact ⟨hw hyw, hyw, fun z hz hzw ↦ hmin z (Or.inr ⟨φ, Or.inl hz⟩) hzw⟩
  · rintro ⟨hyφ, hyw, hmin⟩
    refine ⟨Or.inr (Set.mem_iUnion.mpr ⟨φ, hyφ⟩), hyw, ?_⟩
    intro z hz hzw
    rcases hz with hz | ⟨ψ, hz | ⟨hform, hz⟩⟩
    · exact Set.disjoint_left.mp (f.property φ).2.1 (α.val.property.rel_dom hz).2 hyφ
    · have hψφ : ψ = φ := by
        by_contra hc
        exact Set.disjoint_left.mp ((f.property ψ).2.2 φ hc)
          ((f ψ).val.property.rel_dom hz).2 hyφ
      subst hψφ; exact hmin z hz hzw
    · exact Set.disjoint_left.mp (f.property φ).2.1 (branch_implies_node ψ hform) (hw hzw)

/-- Within a copy, `seq`'s outcome filter coincides with the copy's.  The extra branch
conjunct `φ` in the `seq` formula does not change satisfiability because `φ` is satisfiable
and ranges over the (disjoint) nodes of `α`. -/
lemma seq_filter_copy (α β : Lpofin l) (f : CopyFn α β) (φ : α.branches)
    (w : Finset Node) (hw : ↑w ⊆ (f φ).nodes) {x : Node} (hx : x ∈ w) (r : Bool) :
    (seq α β f).filter_by_outcome w x r = (f φ).filter_by_outcome w x r := by
  classical
  unfold filter_by_outcome
  ext z
  simp only [Finset.mem_filter]
  refine and_congr_right fun hze => ?_
  have hz : z ∈ (f φ).nodes := hw (Finset.mem_of_mem_erase hze)
  have hxz : x ∈ (f φ).nodes := hw hx
  rw [seq_form_copy α β f φ hz]
  have hreassoc :
      (((f φ).form z).and φ.val).and (bif r then Form.literal x else (Form.literal x).not) =
      (((f φ).form z).and (bif r then Form.literal x else (Form.literal x).not)).and φ.val := by
    ext v; simp only [Form.and]; tauto
  rw [hreassoc]
  have hA : ((f φ).form z).DependsOn (f φ).nodes := by
    refine Form.DependsOn.monotone _ ?_ ((f φ).val.property.form z hz).1
    intro y hy; exact ((f φ).val.property.rel_dom hy).1
  have hlit : (bif r then Form.literal x else (Form.literal x).not).DependsOn (f φ).nodes := by
    cases r <;> simp only [cond_true, cond_false]
    · exact Form.DependsOn.monotone _ (by simpa using hxz) (Form.DependsOn.literal (x := x)).not
    · exact Form.DependsOn.monotone _ (by simpa using hxz) (Form.DependsOn.literal (x := x))
  have hp : (((f φ).form z).and
      (bif r then Form.literal x else (Form.literal x).not)).DependsOn (f φ).nodes := by
    have := Form.DependsOn.and hA hlit; rwa [Set.union_self] at this
  exact sat_and_indep hp (branch_dependsOn α φ.property) ((f.property φ).2.1.symm)
    (branch_sat α φ.property)

/-- The copy phase, by strong induction on the remaining set `w ⊆ (f φ).nodes`.
Mirror of `lin_rec_guard_right_aux`, using `seq_next_copy`, `seq_lab_copy`,
`seq_filter_copy`. -/
lemma seq_lin_rec_copy {t : Type → Type} {s act test : Type}
    [Linearizable t s] [∀ {β : Type}, Preorder (t β)] [∀ {β : Type}, OrderBot (t β)]
    [PartialOrder act] [Sem act s (t s)]
    [PartialOrder test] [Sem test s (t Bool)]
    (α β : Lpofin (Label act test)) (f : CopyFn α β) (φ : α.branches)
    (w : Finset Node) (hw : ↑w ⊆ (f φ).nodes) :
    ((seq α β f).lin_rec w : s → t s) = (f φ).lin_rec w := by
  classical
  induction w using Finset.strongInduction with
  | H w ih =>
    ext σ
    unfold lin_rec
    by_cases he : w = ∅
    · simp only [he, ↓reduceIte]
    · simp only [he, ↓reduceIte]
      refine Nondet.nondet_congr (finsetCongrEq (seq_next_copy α β f φ w hw)) ?_
      ext ⟨y, hy⟩
      have hyw : y ∈ w := (Finset.mem_filter.mp hy).2.1
      have hyφ : y ∈ (f φ).nodes := hw hyw
      simp only [lin_node, Function.comp_apply]
      rw [seq_lab_copy α β f φ hyφ]
      match hl : (f φ).lab y with
      | Label.bot => rfl
      | Label.fork =>
        simp only
        exact congrFun (ih (w.erase y) (Finset.erase_ssubset hyw)
          (fun _ h ↦ hw (Finset.mem_of_mem_erase h))) σ
      | Label.act ac =>
        simp only; congr 1; funext τ
        exact congrFun (ih (w.erase y) (Finset.erase_ssubset hyw)
          (fun _ h ↦ hw (Finset.mem_of_mem_erase h))) τ
      | Label.test bb =>
        simp only; congr 1; funext rr
        rw [seq_filter_copy α β f φ w hw hyw rr]
        exact congrFun (ih ((f φ).filter_by_outcome w y rr)
          (Finset.ssubset_of_subset_of_ssubset filter_by_outcome_sub_erase
            (Finset.erase_ssubset hyw))
          (fun z hz ↦ hw (filter_by_outcome_sub_erase hz |> Finset.mem_of_mem_erase))) σ

/-- Linearizing `seq` on a whole copy equals linearizing `β` (copies are isomorphic to `β`). -/
lemma seq_lin_copy {t : Type → Type} {s act test : Type}
    [Linearizable t s] [∀ {β : Type}, Preorder (t β)] [∀ {β : Type}, OrderBot (t β)]
    [PartialOrder act] [Sem act s (t s)]
    [PartialOrder test] [Sem test s (t Bool)]
    (α β : Lpofin (Label act test)) (f : CopyFn α β) (φ : α.branches) :
    ((seq α β f).lin_rec (f φ).nodes_finset : s → t s) = lin β := by
  rw [seq_lin_rec_copy α β f φ (f φ).nodes_finset
    (fun _ hx ↦ (f φ).property.mem_toFinset.mp hx)]
  exact lin_isomorphic (f.property φ).1

lemma lin_seq {t : Type → Type} {s act test : Type}
    [Linearizable t s]
    [∀ {β : Type}, Preorder (t β)] [∀ {β : Type}, OrderBot (t β)]
    [PartialOrder act] [Sem act s (t s)]
    [PartialOrder test] [Sem test s (t Bool)]
    (α β : Lpofin (Label act test)) (f : CopyFn α β) :
    (lin (seq α β f) : s → t s) = fun σ ↦ lin α σ >>= lin β := by sorry

end Lpofin
