import Mathlib
import ConjointSD.ConjointIdentification
import ConjointSD.StatusConjointDesign
import ConjointSD.Assumptions

open Filter MeasureTheory ProbabilityTheory
open scoped Topology BigOperators

noncomputable section
namespace ConjointSD

/-!
## 1) Conjoint identification wrappers
-/

section Identification

variable {Ω : Type*} [MeasurableSpace Ω]
variable (μexp : Measure Ω) [ProbMeasureAssumptions μexp]
variable {Attr : Type*} [MeasurableSpace Attr] [MeasurableSingletonClass Attr]
variable (X : Ω → Attr) (Y : Attr → Ω → ℝ) (Yobs : Ω → ℝ)

/-- Identification: observed conditional mean among `X = x0` equals the potential-outcome mean. -/
theorem paper_identifies_potMean_from_condMean
    (h : ConjointIdRandomized (μexp := μexp) (X := X) (Y := Y) (Yobs := Yobs))
    (x0 : Attr)
    (hpos : μexp (eventX (X := X) x0) ≠ 0) :
    condMean (κ := μexp) Yobs (eventX (X := X) x0) = potMean (κ := μexp) Y x0 :=
  identified_potMean_from_condMean (μexp := μexp) (X := X) (Y := Y) (Yobs := Yobs) h x0 hpos

/-- Identification: AMCE equals a difference of observed conditional means. -/
theorem paper_identifies_amce_from_condMeans
    (h : ConjointIdRandomized (μexp := μexp) (X := X) (Y := Y) (Yobs := Yobs))
    (hpos : ∀ x, μexp (eventX (X := X) x) ≠ 0)
    (x x' : Attr) :
    (condMean (κ := μexp) Yobs (eventX (X := X) x')
      - condMean (κ := μexp) Yobs (eventX (X := X) x))
      =
    amce (κ := μexp) Y x x' :=
  identified_amce_from_condMeans (μexp := μexp) (X := X) (Y := Y) (Yobs := Yobs) h hpos x x'

end Identification

/-!
## 1b) Status-conjoint identification wrappers
-/

section StatusIdentification

variable {Respondent : Type u} [MeasurableSpace Respondent]
variable (μResp : Measure Respondent) [ProbMeasureAssumptions μResp]
variable (Yresp : StatusProfile → Respondent → TaskSlot → ℝ)

/-- Identification for the concrete status conjoint: conditional mean equals potential mean. -/
theorem paper_identifies_potMean_from_condMean_status
    (hmeas :
      ∀ p, Measurable (fun rt : Respondent × TaskSlot => Yresp p rt.fst rt.snd))
    (hmeasObs : Measurable (statusYobs (Yresp := Yresp)))
    (hbound : ∀ p r t, |Yresp p r t| ≤ 100)
    (x0 : StatusProfile) :
    condMean (κ := μStatus (μResp := μResp))
      (statusYobs (Yresp := Yresp)) (eventX (X := statusX) x0)
        =
    potMean (κ := μStatus (μResp := μResp)) (statusY (Yresp := Yresp)) x0 := by
  have h :=
    status_id_randomized (μResp := μResp) (Yresp := Yresp) hmeas hmeasObs hbound
  have hpos := status_event_pos (μResp := μResp)
  exact
    paper_identifies_potMean_from_condMean
      (μexp := μStatus (μResp := μResp))
      (X := statusX) (Y := statusY (Yresp := Yresp))
      (Yobs := statusYobs (Yresp := Yresp)) h x0 (hpos x0)

end StatusIdentification


end ConjointSD
