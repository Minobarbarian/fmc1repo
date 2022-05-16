------------------------------------------------
-- Axiomas:
------------------------------------------------
  axiom ZA_Ass (a b c: ℤ) : (a + b) + c = a + (b + c)
  axiom ZA_idR (a : ℤ) : a = a + 0
  axiom ZA_invR (a : ℤ) : 0 = a + (-a)
  axiom ZA_Com (a b : ℤ) : a + b = b + a

  axiom ZM_Ass (a b c : ℤ) : (a * b) * c = a * (b * c)
  axiom ZM_idR (a : ℤ) : a = a * 1
  axiom ZM_Com (a b : ℤ) : a * b = b * a

  axiom Z_DistR (a b c : ℤ) : (a + b) * c = a * c + b * c
  axiom Z_NZD (a b : ℤ) : (a * b) = 0 → a = 0 ∨ b = 0

  axiom ZP_A (x y > 0) : x + y > 0
  axiom ZP_M (x y > 0) : x * y > 0

------------------------------------------------
-- Lemmas da Esquerda:
------------------------------------------------
  lemma ZA_idL: ∀ (a : ℤ), a = 0 + a :=
    begin
      intro a,
      have h : a = a + 0 := ZA_idR a,
      rw ZA_Com a 0 at h,
      exact h,
    end
  lemma ZA_invL: ∀ (a : ℤ), 0 = (-a) + a :=
    begin
      intro a,
      have h : 0 = a + (-a) := ZA_invR a,
      rw ZA_Com a (-a) at h,
      exact h,
    end
  lemma ZM_idL: ∀ (a : ℤ), a = 1 * a :=
    begin
      intro a,
      have h : a = a * 1 := ZM_idR a,
      rw ZM_Com a 1 at h,
      exact h,
    end
  lemma Z_DistL: ∀ (a b c : ℤ), c * (a + b) = c * a + c * b:=
    begin
      intros a b c,
      have h : (a + b) * c = a * c + b * c := Z_DistR a b c,
      rw ZM_Com (a + b) c at h,
      rw ZM_Com a c at h,
      rw ZM_Com b c at h,
      exact h,
    end
------------------------------------------------
-- Lemmas Extras:
------------------------------------------------
  lemma ZA_PF: ∀ (a b u: ℤ), a = b → a + u = b + u :=
    begin
      intros a b u h,
      have h1: a + u = a + u,
      refl,
      conv{
        to_rhs,
        rw ←h,
      },
    end
  lemma ZA_Trans: ∀ (a b c : ℤ), (a = c ∧ b = c) → a = b :=
    begin
      intros a b c,
      intro h,
      cases h with h1 h2,
      conv{
        to_lhs,
        rw h1,
      },
      conv{
        to_rhs,
        rw h2,
      },
    end
------------------------------------------------
-- Teoremas de Anulamento:
------------------------------------------------
  theorem ZM_AnR: ∀ (a : ℤ), a * 0 = 0 :=
    begin
      intro a,
      have h: a + (a * 0) = a,
      conv{
        to_rhs,
        rw ZM_idR a,
        rw ZA_idR 1,
        rw Z_DistL 1 0 a,
        congr,
        rw ←ZM_idR a,
        skip,
        skip,
      },
      have h1: (a + (a * 0)) = a → (a + (a * 0)) + (-a) = a + (-a) := ZA_PF (a + (a * 0)) a (-a),
      have h2: (a + (a * 0)) + (-a) = a + (-a) := h1 h,
      rw ZA_Ass a (a * 0) (-a) at h2,
      rw ZA_Com (a * 0) (-a) at h2,
      rw ←ZA_Ass a (-a) (a * 0) at h2,
      rw ←ZA_invR a at h2,
      rw ←ZA_idL (a * 0) at h2,
      exact h2,
    end
  theorem ZM_AnL: ∀ (a : ℤ), 0 * a = 0 :=
    begin
      intro a,
      have h: a * 0 = 0 := ZM_AnR a,
      rw ZM_Com a 0 at h,
      exact h,
    end
------------------------------------------------
-- Teoremas de Negação:
------------------------------------------------
  theorem ZS_Neg: ∀ (x : ℤ), (-1) * x = -x :=
    begin
      intro x,
      have h: x + (-1) * x = 0,
      have h1: x * 0 = 0 := ZM_AnR x,
      conv{
        to_rhs,
        rw ←h1,
        rw ZA_invR 1,
        rw Z_DistL 1 (-1) x,
        rw ←ZM_idR x,
        rw ZM_Com x (-1),
      },
      have h2: (x + (-1) * x) = 0 → (x + (-1) * x) + (-x) = 0 + (-x) := ZA_PF (x + (-1) * x) 0 (-x),
      have h3: (x + (-1) * x) + (-x) = 0 + (-x) := h2 h,
      rw ZA_Ass x ((-1) * x) (-x) at h3,
      rw ZA_Com ((-1) * x) (-x) at h3,
      rw ←ZA_Ass x (-x) ((-1) * x) at h3,
      rw ←ZA_invR x at h3,
      rw ←ZA_idL ((-1) * x) at h3,
      rw ←ZA_idL (-x) at h3,
      exact h3,
    end
  theorem ZS_DNeg: ∀ (x : ℤ), -(-x) = x :=
    begin
      intro x,
      conv{
        to_lhs,
        rw ZA_idR (-(-x)),
        rw ZA_invL x,
        rw ←ZA_Ass (-(-x)) (-x) x,
        rw ←ZA_invL (-x),
        rw ←ZA_idL x,
      },
    end
  theorem ZS_MNegU: ∀ (x y : ℤ), -x * y = -(x * y) :=
    begin
      intros x y,
      have h: x * y + (-x) * y = 0,
      conv{
        to_lhs,
        rw ←Z_DistR x (-x) y,
        rw ←ZA_invR x,
        rw ZM_AnL y,
      },
      have h1: (x * y + (-x) * y) = 0 → (x * y + (-x) * y) + -(x * y) = 0 + -(x * y) := ZA_PF (x * y + (-x) * y) 0 (-(x * y)),
      have h2: (x * y + (-x) * y) + -(x * y) = 0 + -(x * y) := h1 h,
      rw ZA_Ass (x * y) (-x * y) (-(x * y)) at h2,
      rw ←ZA_Com (-(x * y)) (-x * y) at h2,
      rw ←ZA_Ass (x * y) (-(x * y)) (-x * y) at h2,
      rw ←ZA_invR (x * y) at h2,
      rw ←ZA_idL (-x * y) at h2,
      rw ←ZA_idL (-(x * y)) at h2,
      exact h2,
    end
  theorem ZS_MNegD: ∀ (x y : ℤ), x * (-y) = -(x * y) :=
    begin
      intros x y,
      have h: x * y + x * (-y) = 0,
      conv{
        to_lhs,
        rw ←Z_DistL y (-y) x,
        rw ←ZA_invR y,
        rw ZM_AnR x,
      },
      have h1: (x * y + x * (-y)) = 0 → (x * y + x * (-y)) + -(x * y) = 0 + - (x * y) := ZA_PF (x * y + x * (-y)) 0 (-(x * y)),
      have h2: (x * y + x * (-y)) + -(x * y) = 0 + - (x * y) := h1 h,
      rw ZA_Ass (x * y) (x * -y) (-(x * y)) at h2,
      rw ZA_Com (x * -y) (-(x * y)) at h2,
      rw ←ZA_Ass (x * y) (-(x * y)) (x * -y) at h2,
      rw ←ZA_invR (x * y) at h2,
      rw ←ZA_idL (x * -y) at h2,
      rw ←ZA_idL (-(x * y)) at h2,
      exact h2,
    end
  theorem ZS_MNegT: ∀ (x y : ℤ), (-x) * y = x * (-y) :=
    begin
      intros x y,
      conv{
        to_rhs,
        rw ZS_MNegD x y,
        rw ←ZS_MNegU x y,
      },
    end
  theorem ZS_PNeg: ∀ (x y : ℤ), (-x) * (-y) = x * y :=
    begin
      intros x y,
      conv{
        to_lhs,
        rw ←ZS_Neg x,
        rw ZM_Ass (-1) x (-y),
        rw ZS_Neg (x * (-y)),
        rw ZS_MNegD x y,
        rw ZS_DNeg,
      },
    end
  theorem ZS_TNegU: ∀ (x y : ℤ), -(x + (-y)) = y + (-x) :=
    begin
      intros x y,
      conv{
        to_lhs,
        rw ←ZS_Neg,
        rw Z_DistL x (-y) (-1),
        rw ZS_Neg x,
        rw ZS_Neg (-y),
        rw ZS_DNeg,
        rw ZA_Com,
      },
    end
  theorem ZS_TNegD: ∀ (x y : ℤ), -(x + y) = -x + (-y) :=
    begin
      intros x y,
      conv{
        to_lhs,
        rw ←ZS_Neg,
        rw Z_DistL x y (-1),
        rw ZS_Neg x,
        rw ZS_Neg y,
      },
    end
------------------------------------------------
-- Teoremas de Passar pro Outro Lado:
------------------------------------------------
  theorem ZA_polu: ∀ (a b c : ℤ), a + b = c ↔ a = c + (-b) :=
    begin
      intros a b c,
      split,
      intro h,
      conv{
        to_lhs,
        rw ZA_idR a,
        rw ZA_invR c,
        congr,
        skip,
        congr,
        skip,
        rw ←h,
        rw ZS_TNegD,
      },
      conv{
        to_lhs,
        rw ←ZA_Ass c (-a) (-b),
        rw ZA_Com c (-a),
        rw ZA_Ass (-a) c (-b),
        rw ←ZA_Ass a (-a) (c + (-b)),
        rw ←ZA_invR,
        rw ←ZA_idL,
      },
      intro h,
      conv{
        to_rhs,
        rw ZA_idR c,
        rw ZA_invR a,
        congr,
        skip,
        congr,
        skip,
        rw h,
        rw ZS_TNegU,
        rw ZA_Com,
      },
      conv{
        to_rhs,
        rw ←ZA_Ass a (-c) b,
        rw ZA_Com a (-c),
        rw ZA_Ass (-c) a b,
        rw ←ZA_Ass c (-c) (a + b),
        rw ←ZA_invR,
        rw ←ZA_idL,
      },
    end
  theorem ZA_pold: ∀ (a b c : ℤ), a + b = c ↔ b = c + (-a) :=
    begin
      intros a b c,
      split,
      intro h,
      conv{
        to_lhs,
        rw ZA_idR b,
        rw ZA_invR c,
        congr,
        skip,
        congr,
        skip,
        rw ←h,
        rw ZS_TNegD,
        rw ZA_Com,
      },
      conv{
        to_lhs,
        rw ←ZA_Ass c (-b) (-a),
        rw ZA_Com c (-b),
        rw ZA_Ass (-b) c (-a),
        rw ←ZA_Ass b (-b) (c + (-a)),
        rw ←ZA_invR,
        rw ←ZA_idL,
      },
      intro h,
      conv{
        to_rhs,
        rw ZA_idR c,
        rw ZA_invR b,
        congr,
        skip,
        congr,
        skip,
        rw h,
        rw ZS_TNegU,
        rw ZA_Com,
      },
      conv{
        to_rhs,
        rw ←ZA_Ass b (-c) a,
        rw ZA_Com b (-c),
        rw ZA_Ass (-c) b a,
        rw ←ZA_Ass c (-c) (b + a),
        rw ←ZA_invR,
        rw ←ZA_idL,
        rw ZA_Com,
      },
    end
  theorem ZA_polt: ∀ (a b : ℤ), a = b ↔ a + (-b) = 0 :=
    begin
      intros a b,
      split,
      intro h,
      conv{
        to_lhs,
        rw h,
        rw ←ZA_invR,
      },
      intro h,
      conv{
        to_rhs,
        rw ZA_idR b,
        rw ←h,
        rw ZA_Com a (-b),
        rw ←ZA_Ass b (-b) (a),
        rw ←ZA_invR,
        rw ←ZA_idL,
      },
    end
------------------------------------------------
-- Teoremas de Cancelamento:
------------------------------------------------
  theorem ZA_CanR: ∀ (a b c : ℤ), a + c = b + c → a = b :=
    begin
      intros a b c h,
      conv{
        to_lhs,
        rw ZA_idR a,
        rw ZA_invR c,
        rw ←ZA_Ass a c (-c),
        rw h,
        rw ZA_Ass b c (-c),
        rw ←ZA_invR,
        rw ←ZA_idR,
      },
    end
  theorem ZA_CanL: ∀ (a b c : ℤ), c + a = c + b → a = b :=
    begin
      intros a b c h,
      have h1: a + c = b + c → a = b := ZA_CanR a b c,
      rw ←ZA_Com a c at h,
      rw ←ZA_Com b c at h,
      have h2: a = b := h1 h,
      exact h2,
    end
  theorem ZM_CanR: ∀ (a b c : ℤ), a * c = b * c →  c = 0 ∨ a = b :=
    begin
      intros a b c h,
      have h1: (a + (-b)) * c = 0,
      conv{
        to_lhs,
        rw Z_DistR,
        rw h,
        rw ZS_MNegU,
        rw ←ZA_invR,
      },
      have h2: (a + (-b)) * c = 0 → (a + (-b)) = 0 ∨ c = 0 := Z_NZD (a + (-b)) c,
      have h3: (a + (-b)) = 0 ∨ c = 0 := h2 h1,
      cases h3 with hig hc,
      right,
      have h4: a = b ↔ a + (-b) = 0 := ZA_polt a b,
      cases h4,
      have h5: a = b := h4_mpr hig,
      exact h5,
      left,
      exact hc,
    end
------------------------------------------------
-- Unicidades:
------------------------------------------------
  theorem ZA_IdUni: ∀ (a b: ℤ), (∃ x : ℤ, a + x = a) ∧ ((a + b = a) ∧ (b + a = a) → b = 0):=
    begin
      intros a b,
      split,
      existsi (a + (-a)),
      rw ←ZA_invR,
      rw ←ZA_idR,
      intro h,
      cases h with hab hba,
      have h: (a + b) = a ↔ (a + b) + (-a) = 0 := ZA_polt (a + b) a,
      cases h,
      have h2: (a + b) + (-a) = 0 := h_mp hab,
      conv{
        to_rhs,
        rw ←h2,
        rw ZA_Com,
        rw ←ZA_Ass,
        rw ←ZA_invL,
        rw ←ZA_idL,
      },
    end
  theorem ZM_IdUni: ∀ (a b: ℤ), (∃ x : ℤ, a * x = a) ∧ ((a * b = a) ∧ (b * a = a) → b = 1):=
    begin
      intros a b,
      split,
      existsi (1 + (a + (-a))),
      conv{
        to_lhs,
        rw ←ZA_invR,
        rw ←ZA_idR,
        rw ←ZM_idR,
      },
      intro h,
      cases h with hab hba,
      sorry,
    end
  theorem ZA_InvUni: ∀ (x : ℤ), (∃ k : ℤ, x + k = 0) ∧ (∀ (u : ℤ), (u + x = 0 ∧ x + u = 0) → u = -x) :=
    begin
      intro x,
      split,
      existsi (0 + (-x)),
      conv{
        to_lhs,
        rw ←ZA_idL (-x),
        rw ←ZA_invR x,
      },
      intros u h,
      cases h with ux xu,
      have h: (x + u) = 0 → (x + u) + (-x) = 0 + (-x) := ZA_PF (x + u) 0 (-x),
      have h1: (x + u) + (-x) = 0 + (-x) := h xu,
      rw ZA_Ass x u (-x) at h1,
      rw ZA_Com u (-x) at h1,
      rw ←ZA_Ass x (-x) u at h1,
      rw ←ZA_invR x at h1,
      rw ←ZA_idL u at h1,
      rw ←ZA_idL (-x) at h1,
      exact h1,
    end
  theorem ZA_ResUni: ∀ (a b: ℤ), (∃ x : ℤ, a + x =b) ∧ (∀ (x y: ℤ), (a + x = b) ∧ (a + y = b) → x = y) :=
    begin
      intros a b,
      split,                            -- Existência
      existsi (-a + b),
      rw ←ZA_Ass a (-a) b,
      rw ←ZA_invR,
      rw ←ZA_idL,                       -- Fim de Existência
      intros x y h,                     -- Unicidade
      cases h with hax hay,
      have h: a + x = a + y,
      conv{
        to_lhs,
        rw hax,
      },
      conv{
        to_rhs,
        rw hay,
      },
      have h1: a + x = a + y → x = y := ZA_CanL x y a,
      have h2: x = y := h1 h,
      exact h2,                         -- Fim da Unicidade
    end
------------------------------------------------
-- Z_NZD pelo ZM_CanR:
------------------------------------------------
  theorem Z_NZD': ∀ (a b : ℤ), a * b = 0 → a = 0 ∨ b = 0 :=
    begin
      intros a b h,
      have h1: a * b = 0 * b → b = 0 ∨ a = 0 := ZM_CanR a 0 b,
      rw ←ZM_AnL b at h,
      have h2: b = 0 ∨ a = 0 := h1 h,
      cases h2,
      right,
      exact h2,
      left,
      exact h2,
    end
------------------------------------------------
-- Propriedades divisibilidade:
------------------------------------------------
  theorem ZD_p1: ∀ (a : ℤ), ∃ x : ℤ, a = x * 1 :=
    begin
      intro a,
      existsi a,
      conv{
        to_rhs,
        rw ←ZM_idR,
      },
    end
  theorem ZD_p2: ∀ (a : ℤ), ∃ x : ℤ, 0 = x * a :=
    begin
      intro a,
      existsi (a * 0),
      rw ZM_AnR,
      rw ZM_AnL,
    end
  theorem ZD_p3: ∀ (a b x : ℤ), (∃ k : ℤ, b = k * a) → ∃ l : ℤ, b * x = l * a :=
    begin
      intros a b x,
      intro h,
      cases h with k hb,
      existsi k,
      conv{
        to_rhs,
        rw ←hb,
      },
      sorry,
    end