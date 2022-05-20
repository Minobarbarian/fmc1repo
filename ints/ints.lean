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

  axiom ZP_A (a b > 0) : a + b > 0
  axiom ZP_M (a b > 0) : a * b > 0
  axiom ZP_Tri (a : ℤ) : (a = 0) ∨ (a > 0) ∨ (a < 0)
  axiom ZP_Tri' (a : ℤ) : (a = 0 ∧ ¬(a < 0) ∧ ¬(a > 0)) ∨ (a > 0 ∧ ¬(a < 0) ∧ ¬(a = 0)) ∨ (a < 0 ∧ ¬(a > 0) ∧ ¬(a = 0))

------------------------------------------------
-- Definições:
------------------------------------------------
  
  def abs (x : ℤ) := if (x > 0 ∨ x = 0) then x else -x
  notation | x | := abs x
  def applyabs (x : ℤ) := | x | = abs x
  notation x < y := 0 < (y + (-x))
  def unit' (x : ℤ) := ∃ k : ℤ, x * k = 1
  def is_ZM_idR (w : ℤ) := ∀ (a : ℤ), a * w = a
  
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
  lemma ZA_PF: ∀ (a b u : ℤ), a = b → a + u = b + u :=
    begin
      intros a b u h,
      have h1: a + u = a + u,
      refl,
      conv{
        to_rhs,
        rw ←h,
      },
    end
  lemma Z_Trans: ∀ (a b c : ℤ), (a = c ∧ b = c) → a = b :=
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
  theorem ZM_CanR: ∀ (a b c : ℤ), a * c = b * c → c = 0 ∨ a = b :=
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
  theorem ZM_CanL: ∀ (a b c : ℤ), c * a = c * b → c = 0 ∨ a = b :=
    begin
      intros a b c h,
      have h1: a * c = b * c → c = 0 ∨ a = b := ZM_CanR a b c,
      rw ←ZM_Com a c at h,
      rw ←ZM_Com b c at h,
      have h2: c = 0 ∨ a = b := h1 h,
      exact h2,
    end
------------------------------------------------
-- Existências e Unicidades:
------------------------------------------------
  theorem ZA_ResExi: ∀ (a b: ℤ), (∃ x : ℤ, a + x = b) :=
    begin
      intros a b,
      existsi (-a + b),
      rw ←ZA_Ass a (-a) b,
      rw ←ZA_invR,
      rw ←ZA_idL,
    end
  theorem ZA_ResUni: ∀ (a b x y: ℤ), ((a + x = b) ∧ (a + y = b)) → x = y :=
    begin
      intros a b x y h,
      cases h,
      have h: a + x = a + y,
      conv{
        to_lhs,
        rw h_left,
        rw ←h_right,
      },
      have h1: a + x = a + y → x = y := ZA_CanL x y a,
      have h2: x = y := h1 h,
      exact h2,
    end
  theorem ZA_IdExi: ∀ (a : ℤ), ∃ x : ℤ, a + x = a:=
    begin
      intro a,
      existsi (a + (-a)),
      rw ←ZA_invR,
      rw ←ZA_idR,
    end
  theorem ZA_IdUni: ∀ (a b: ℤ), ((a + b = a) ∧ (b + a = a)) → b = 0 :=
    begin
      intros a b h,
      cases h with hab hba,
      have h: a + 0 = a,
      have h1: a = a + 0 := ZA_idR a,
      conv{
        to_lhs,
        rw ←ZA_idR,
      },
      have h1: ((a + b = a) ∧ (a + 0 = a)) → b = 0 := ZA_ResUni a a b 0,
      have h2: (a + b = a) ∧ (a + 0 = a),
      split,
      exact hab,
      exact h,
      have h3: (b = 0) := h1 h2,
      exact h3,
    end
  theorem ZM_IdExi: ∀ (a : ℤ), ∃ x : ℤ, a * x = a:=
    begin
      intro a,
      existsi (1 + (a + (-a))),
      conv{
        to_lhs,
        rw ←ZA_invR,
        rw ←ZA_idR,
        rw ←ZM_idR,
      },
    end
  theorem ZM_IdUni: ∀ (a u v: ℤ), (is_ZM_idR u ∧ is_ZM_idR v) → u = v :=
    begin
      intros a u v h,
      cases h with hu hv,
      calc
        u = u * v : by rw [hv u]
      ... = v * u : by rw [ZM_Com v u]
      ... = v : by rw [hu v],
    end
  theorem ZA_InvExi: ∀ (x : ℤ), (∃ k : ℤ, x + k = 0) :=
    begin
      intro x,
      existsi (0 + (-x)),
      conv{
        to_lhs,
        rw ←ZA_idL (-x),
        rw ←ZA_invR x,
      },
    end
  theorem ZA_InvUni: ∀ (x u : ℤ), ((u + x = 0) ∧ (x + u = 0)) → u = -x :=
    begin
      intros x u h,
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
  theorem ZD_p3: ∀ (a b x : ℤ), (∃ k : ℤ, b = k * a) → (∃ l : ℤ, b * x = l * a) :=
    begin
      intros a b x,
      intro h,
      cases h with k hb,
      existsi (k * x),
      conv{
        to_lhs,
        rw hb,
        rw ZM_Ass,
        rw ZM_Com a x,
        rw ←ZM_Ass,
      },
    end
  theorem ZD_p4: ∀ (a b : ℤ), (∃ k : ℤ, b = a * k) → (∃ l : ℤ, (-b) = a * l) ∧ (∃ m : ℤ, b = (-a) * m) :=
    begin
      intros a b h,
      cases h with k h,
      split,
      existsi (-k),
      conv{
        to_rhs,
        rw ZS_MNegD,
        rw ←h,
      },
      existsi (-k),
      conv{
        to_rhs,
        rw ZS_PNeg,
        rw ←h,
      },
    end
  theorem ZD_p5: ∀ (a b c: ℤ), (∃ k : ℤ, b = a * k) ∧ (∃ l : ℤ, c = a * l) → (∃ m : ℤ, b + c = a * m) :=
    begin
      intros a b c h,
      cases h with hek hel,
      cases hek with k hk,
      cases hel with l hl,
      existsi (k + l),
      conv{
        to_rhs,
        rw Z_DistL,
        rw ←hk,
        rw ←hl,
      },
    end
  theorem ZD_p6: ∀ (a b c x y: ℤ), (∃ k : ℤ, b = a * k) ∧ (∃ l : ℤ, c = a * l) → (∃ m : ℤ, b * x + c * y = a * m) :=
    begin
      intros a b c x y h,
      cases h with hek hel,
      cases hek with k hk,
      cases hel with l hl,
      existsi (k * x + l * y),
      conv{
        to_rhs,
        rw Z_DistL,
        congr,
        rw ZM_Com k x,
        rw ←ZM_Ass,
        rw ZM_Com,
        skip,
        rw ZM_Com l y,
        rw ←ZM_Ass,
        rw ZM_Com,
      },
      conv{
        to_lhs,
        congr,
        rw hk,
        rw ZM_Com a k,
        rw ZM_Ass,
        skip,
        rw hl,
        rw ZM_Com a l,
        rw ZM_Ass,
      },
    end
  theorem ZD_p7: ∀ (a b: ℤ), ((∃ k : ℤ, b = a * k) ∧ (b = 0 → false)) → (|a|) < (|b|) ∨ (|a|) = (|b|) :=
    begin
      intros a b h,
      cases h,
      cases h_left with k hk,
      have h: (a = 0) ∨ (a > 0) ∨ (a < 0) := ZP_Tri a,
      have h1: (b = 0) ∨ (b > 0) ∨ (b < 0) := ZP_Tri b,
      cases h,
      cases h1,
      contradiction,
      cases h1,
      have h2: a > 0 ∨ a = 0,
      right,
      exact h,
      left,
      show (|a|) < (|b|),
    end
  theorem ZD_p8: ∀ (a b c: ℤ), ((c = 0) → false) → ((∃ k : ℤ, b = a * k) ↔ (∃ l : ℤ, c * b = (c * a) * l)) :=
    begin
      intros a b c hnc,
      split,
      intro hek,
      cases hek with k hk,
      existsi (k),
      conv{
        to_lhs,
        rw hk,
        rw ←ZM_Ass,
      },
      intro hel,
      cases hel with l hl,
      have h: c * (b + -(a * l)) = 0,
      conv{
        to_lhs,
        rw Z_DistL,
        rw ZS_MNegD,
        rw ←ZM_Ass,
        rw hl,
        rw ←ZA_invR,
      },
      have h1: (c * (b + -(a * l))) = 0 → c = 0 ∨ (b + -(a * l)) = 0 := Z_NZD c (b + -(a * l)),
      have h2: c = 0 ∨ (b + -(a * l)) = 0 := h1 h,
      cases h2,
      contradiction,
      existsi l,
      conv{
        to_rhs,
        rw ZA_idR (a * l),
        rw ←h2,
        rw ZA_Com b (-(a * l)),
        rw ←ZA_Ass (a * l) (-(a * l)) (b),
        rw ←ZA_invR,
        rw ←ZA_idL b,
      },
    end
  theorem ZD_Refl: ∀ (a: ℤ), (∃ k : ℤ, a = a * k) :=
    begin
      intro a,
      existsi (1 + (a +(-a))),
      conv{
        to_rhs,
        rw ←ZA_invR a,
        rw ←ZA_idR 1,
        rw ←ZM_idR a,
      },
    end
  theorem ZD_Trans: ∀ (a b c: ℤ), (∃ k : ℤ, b = a * k) ∧ (∃ l : ℤ, c = b * l) → (∃ m : ℤ, c = a * m) :=
    begin
      intros a b c h,
      cases h with hek hel,
      cases hek with k hk,
      cases hel with l hl,
      have h1: c = a * (k * l),
      conv{
        to_rhs,
        rw ←ZM_Ass,
        rw ←hk,
        rw ←hl,
      },
      existsi (k * l),
      exact h1,
    end
------------------------------------------------
-- Teoremas de Ordem:
------------------------------------------------
------------------------------------------------
-- Irredutível, Primo e Prime:
------------------------------------------------
  theorem Z_IrredPrime: ∀ (a b p : ℤ), (p = a * b → (unit' a ∨ unit' b)) ↔ ((∃ k : ℤ, a * b = p * k) → unit' a ∨ unit' b) :=
    begin
      intros a b p,
      split,
      intro h,
      intro hek,
      cases hek with k hk,
      apply h,
      sorry,
      intro h,
      intro h1,
      apply h,
      existsi (1 + (a + (-a))),
      conv{
        to_rhs,
        rw ←ZA_invR a,
        rw ←ZA_idR 1,
        rw ←ZM_idR p,
        rw h1,
      },
    end
  theorem Z_IrredPrimo: ∀ (a b p : ℤ), (p = a * b → (unit' a ∨ unit' b)) ↔ (∀ (x : {1, (-1), p, (-p)}), (∃ k : ℤ, p = x * k)) :=
    begin

    end