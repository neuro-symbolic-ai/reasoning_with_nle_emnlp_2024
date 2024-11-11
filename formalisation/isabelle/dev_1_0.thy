theory dev_1_0
imports Main

begin

typedecl entity
typedecl event

consts
  Consumer :: "entity ⇒ bool"
  Feed :: "event ⇒ bool"
  Agent :: "event ⇒ entity ⇒ bool"
  TrophicLevel :: "entity ⇒ bool"
  At :: "event ⇒ entity ⇒ bool"
  Plant :: "entity ⇒ bool"
  Producer :: "entity ⇒ bool"
  Omnivore :: "entity ⇒ bool"

(* Explanation 1: Many consumers feed at more than one trophic level. *)
axiomatization where
  explanation_1: "∃x e y. Consumer x ⟶ (Feed e ∧ Agent e x ∧ TrophicLevel y ∧ At e y)"

(* Explanation 2: Plants are producers are consumers are omnivores. *)
axiomatization where
  explanation_2: "∀x. Plant x ⟶ (Producer x ∧ Consumer x ∧ Omnivore x)"

theorem hypothesis:
  assumes asm: "Omnivore x"
  (* Hypothesis: Omnivores can feed at more than one trophic level. *)
  shows "∃y e. Omnivore x ⟶ (Feed e ∧ Agent e x ∧ TrophicLevel y ∧ At e y)"
proof -
  (* From the premise, we know that x is an omnivore. *)
  from asm have "Omnivore x" by simp
  (* From Explanation 1, we have that many consumers feed at more than one trophic level. *)
  (* Since omnivores are consumers, we can infer that they can also feed at more than one trophic level. *)
  then have "∃y e. Feed e ∧ Agent e x ∧ TrophicLevel y ∧ At e y" sledgehammer
  then show ?thesis <ATP>
qed

end
