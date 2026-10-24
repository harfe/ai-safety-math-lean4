module
public import Mathlib

set_option linter.style.header false

/-! # Logical Induction
This file formalizes the definitions and properties in
`Articles/LogicalInduction.md`.

The main result is `exists_logical_inductor`.
-/


@[expose] public section


namespace LogicalInduction

open Turing

section PropositionalLogic

/-- Prime sentences:
We start out with a collection of prime sentences.
It also comes with an encoding and a finite alphabet.
-/
structure PrimeSentences where
  PS : Type
  nonempty : Nonempty PS
  Alphabet : Type
  finite_alphabet : Finite Alphabet
  encode : PS → List Alphabet
  encode_injective : encode.Injective


variable {ps : PrimeSentences}

/-- Definition (sentences):
The prime sentences act as atoms.
These can be recursively extended using `and`, `or`, `not`.
-/
inductive Sentence (ps : PrimeSentences) where
  | atom (s : ps.PS) : Sentence ps
  | and : Sentence ps → Sentence ps → Sentence ps
  | or : Sentence ps → Sentence ps → Sentence ps
  | not : Sentence ps → Sentence ps

namespace Sentence


/-- Extend alphabet from ps.Alphabet -/
inductive Alphabet (ps : PrimeSentences) where
  | base (val : ps.Alphabet)
  | atom
  | and
  | or
  | not

/-- Encode a Sentence -/
def encode : (p : Sentence ps) → List (Alphabet ps)
  | atom s => Alphabet.atom :: List.map Alphabet.base (ps.encode s)
  | and p1 p2 => Alphabet.and :: p1.encode ++ p2.encode
  | or p1 p2 => Alphabet.or :: p1.encode ++ p2.encode
  | not p1 => Alphabet.not :: p1.encode

/-- Sanity check: injective encoding -/
lemma encode_injective : (@encode ps).Injective := by
  sorry


end Sentence

/-- Definition (world) -/
def World (ps : PrimeSentences) := Sentence ps → Bool

/-- Definition (propositionally consistent): -/
def IsPropConsistent (W : World ps) := ∀ x y,
  (W (Sentence.and x y) = Bool.and (W x) (W y)) ∧
  (W (Sentence.or x y) = Bool.or (W x) (W y)) ∧
  (W (Sentence.not x) = Bool.not (W x))

/-- Sanity check:
there exists a consistent world -/
lemma exists_consistent_world : ∃ (W : World ps), IsPropConsistent W := by
  sorry

/-- Definition (propositionally consistent with a set `D`): -/
def PC (D : Set (Sentence ps)) := {W : World ps | IsPropConsistent W ∧ ∀ x ∈ D, W x = true}

/-- Sanity check:
if a sentence and its opposite are in `D`, then
no world can be consistent with `D`.
-/
lemma nothing_consistent_with_contra (W : World ps) (D : Set (Sentence ps))
    (s1 : Sentence ps) (hs1 : s1 ∈ D) (hs2 : Sentence.not s1 ∈ D) :
    W ∉ PC D := by
  sorry


end PropositionalLogic

section ComputableSequence

/-! some definitions related to computing and encoding.
In general, we will use the `TM2Computable` definition from mathlib,
which is based on `FinTM2`.
`FinTM2` needs finite alphabets.
-/

/- abstract type `β`, and its encoding `eb` over alphabet `βΓ`: -/
variable {β βΓ : Type}
variable (eb : β → List βΓ)


/-- A unary encoding of natural numbers: -/
def encodeUnary (n : ℕ) : List Unit := List.replicate n Unit.unit

/-- Sanity check: injective encoding -/
lemma encodeUnary_injective : encodeUnary.Injective := by
  sorry

/-- Definition (computable sequence):
Uses the `TM2` computation model from Mathlib.
-/
def IsComputableSequence (f : ℕ → β) : Prop := Nonempty <|
  TM2Computable encodeUnary eb f

/-- Definition: efficiently computable sequence.
input `n : ℕ` has to be written in unary.
-/
def IsEfficientlyComputable (f : ℕ → β) : Prop := Nonempty <|
  TM2ComputableInPolyTime encodeUnary eb f

/-- Sanity check:
constants can be computed efficiently. -/
lemma ec_of_constant (b : β) : IsEfficientlyComputable eb (fun _ => b) := by
  sorry

end ComputableSequence

section Encodings

/-- A frequently used codomain: -/
abbrev rat01 := Set.Icc (0 : ℚ) 1

/-- Encoding a rational number as a triple of Nats -/
def ratToList (q : ℚ) : List ℕ := [q.num.sign.toNat, q.num.natAbs, q.den]

/-- Sanity check: -/
lemma ok_ratToList (q : ℚ) :
    ∃ (a b c: ℕ), [a, b, c] = ratToList q ∧
    (a = 0 ∨ a = 1) ∧
    c ≠ 0 ∧ (q : ℝ) = (-1 + 2 * a) * (b : ℝ) / (c : ℝ) := by
  sorry

/-- Encoding a rational number.
Uses `PartrecToTM2.trList` to encode a list of Nats.
-/
def encodeRat (q : ℚ) := PartrecToTM2.trList (ratToList q)

/-- Encoding a single `Nat`.
`trList` adds a `cons` after every element.
-/
def encodeNat (n : ℕ) := PartrecToTM2.trList [n]

/-- Sanity check: injective encoding -/
lemma encodeRat_injective : encodeRat.Injective := by
  sorry

/-- Sanity check: injective encoding -/
lemma encodeNat_injective : encodeNat.Injective := by
  sorry

variable {ps : PrimeSentences}

/-- Definition (belief state) -/
def IsBeliefState (p : Sentence ps → rat01) :=
  (Subtype.val ∘ p).support.Finite

/-- Sanity check:
A belief state is always computable
-/
lemma belief_state_computable (p : Sentence ps → rat01) (hbs : IsBeliefState p) :
    Nonempty <| TM2Computable Sentence.encode (encodeRat ∘ Subtype.val) p := by
  sorry


/-- Sanity check -/
lemma belief_state_of_list (l : List (Sentence ps × rat01))
    (h_nodup : (l.map Prod.fst).Nodup) :
    ∃ p, IsBeliefState p ∧
    (∀ sq ∈ l, p sq.1 = sq.2) ∧
    ∀ s, s ∉ l.map Prod.fst → p s = 0 := by
  sorry

/-- Sanity check -/
lemma list_of_belief_state (p : Sentence ps → rat01) (hbs : IsBeliefState p) :
    ∃ (l : List (Sentence ps × rat01)),
    (l.map Prod.fst).Nodup ∧
    (∀ s, 0 < p s ↔ ⟨s, p s⟩ ∈ l) := by
  sorry


/-- Encoding a list of sentences. -/
def encodeSentenceList (pl : List (Sentence ps)) : List (Sentence.Alphabet ps) :=
  (pl.map Sentence.encode).flatten

/-- Sanity check -/
lemma encodeSentenceList_injective : (@encodeSentenceList ps).Injective := by
  sorry

/-- Encoding a pair in `ℕ × Sentence`. -/
def encodeNatSentence (ns : ℕ × Sentence ps) : List (Unit ⊕ Sentence.Alphabet ps) :=
  List.replicate ns.1 (Sum.inl Unit.unit) ++ List.map Sum.inr (ns.2.encode)

/-- Sanity check -/
lemma encodeNatSentence_injective : (@encodeNatSentence ps).Injective := by
  sorry

/-- Definition (market) -/
def Market (ps : PrimeSentences) := {f : ℕ → Sentence ps → rat01 //
  Nonempty <| TM2Computable encodeNatSentence (encodeRat ∘ Subtype.val) f.uncurry }

abbrev ValuationSequence (ps : PrimeSentences) := ℕ → Sentence ps → unitInterval

namespace Market


/-- A market interpreted as a valuation sequence. -/
def valSequence (P : Market ps) : ValuationSequence ps :=
  fun n s =>
  ⟨P.val n s, by
    unfold unitInterval
    rw [←Rat.cast_zero, ←Rat.cast_one]
    refine Set.mem_preimage.mp ?_
    rw [Rat.preimage_cast_Icc]
    exact Subtype.coe_prop (P.val n s)
  ⟩


end Market

end Encodings


section Deductive


variable {ps : PrimeSentences}


/-- Definition (deductive process) -/
structure DeductiveProcess (ps : PrimeSentences) where
  seq : ℕ → List (Sentence ps)
  computable : IsComputableSequence encodeSentenceList seq
  mono : ∀ n, seq n ⊆ seq (n + 1)

namespace DeductiveProcess


/-- Converting to sets -/
def toSet (D : DeductiveProcess ps) (n : ℕ) : Set (Sentence ps) :=
  {x | x ∈ D.seq n}

/-- Sanity check -/
lemma exists_deductiveProcess_size_n : ∃ (D : DeductiveProcess ps),
    ∀ n, (D.toSet n).ncard = n := by
  sorry


end DeductiveProcess

end Deductive



section Valuation

variable {ps : PrimeSentences}

/-- Valuation features.
We put the rank in the definition.
Can depend on the `rank`th component, but not higher components of V
The product topology gets used on `(Fin (rank + 1) → Sentence ps → unitInterval)`.
-/
structure ValuationFeature (ps : PrimeSentences) where
  rank : ℕ
  map' : (Fin (rank + 1) → Sentence ps → unitInterval) → ℝ
  continuous : Continuous map'

namespace ValuationFeature

/-- Extend valuation features to all indices.
`ValuationFeature.map` can be applied to valuation sequences,
`ValuationFeature.map'` only to initial segments.
-/
def map (vf : ValuationFeature ps) (V : ValuationSequence ps) : ℝ :=
  vf.map' (fun i s => V i.1 s)


/-- Sanity check -/
lemma continuous_map (vf : ValuationFeature ps) : Continuous vf.map := by
  sorry

/-- Whether a valuation feature (identified by `.map`)
has minimal possible rank. -/
def HasMinRank (vf : ValuationFeature ps) : Prop :=
  ∀ (vf2 : ValuationFeature ps), vf.map = vf2.map → vf.rank ≤ vf2.rank

end ValuationFeature


/-- Definition (expressible feature) -/
inductive Expressible (ps : PrimeSentences) where
  | price : ℕ → Sentence ps → Expressible ps
  | rat : ℚ → Expressible ps
  | add : Expressible ps → Expressible ps → Expressible ps
  | mul : Expressible ps → Expressible ps → Expressible ps
  | max : Expressible ps → Expressible ps → Expressible ps
  | safeInv : Expressible ps → Expressible ps


namespace Expressible

/-- Definition hole:
supposed to return the valuation feature that an
expressible feature describes.
-/
def vf : (e : Expressible ps) → ValuationFeature ps := sorry

/-- Pin-down lemma.
We require that the valuation feature of an expressible feature has minimal rank.
This makes the rank of expressible features a semantic property, not a syntactic one.
-/
lemma hasMinRank_of_vf (e : Expressible ps) : e.vf.HasMinRank := by
  sorry

/-- Pin-down lemma for price features -/
lemma ok_vf_price (n : ℕ) (s : Sentence ps)
    (V : ValuationSequence ps) :
    (price n s).vf.map V = V n s := by
  sorry

/-- Pin-down lemma for rational numbers -/
lemma ok_vf_rat (q : ℚ) (V : ValuationSequence ps) :
    (rat q).vf.map V = ↑q := by
  sorry


/-- Pin-down lemma for binary operations.
`Max.max` is the normal maximum on reals here.
-/
lemma ok_vf_bin (e1 e2 : Expressible ps)
    (V : ValuationSequence ps) :
    (add e1 e2).vf.map V = e1.vf.map V + e2.vf.map V ∧
    (mul e1 e2).vf.map V = e1.vf.map V * e2.vf.map V ∧
    (max e1 e2).vf.map V = Max.max (e1.vf.map V) (e2.vf.map V) := by
  sorry

/-- Pin-down lemma for safeInv.
`Max.max` is the normal maximum on reals here.
-/
lemma ok_vf_safeInv (e : Expressible ps) (V : ValuationSequence ps) :
    (safeInv e).vf.map V = (Max.max (e.vf.map V) 1)⁻¹ := by
  sorry


/-- Sanity check:
rank of a price feature is `n`. -/
lemma rank_of_price_feature (n : ℕ) (s : Sentence ps) :
    (price n s).vf.rank = n := by
  sorry

/-- Recursive definition: adding up expressible features from a list -/
noncomputable
def sumOfList : List (Expressible ps) → Expressible ps
  | [] => rat 0
  | e::r => add e (sumOfList r)

/-- Defining the sum of `k` expressible features.
This definition is needed later in `TradingStrategy.cash`.
-/
noncomputable
def sum {k : ℕ} (f : Fin k → Expressible ps) : Expressible ps :=
  sumOfList (List.ofFn f)

/-- Sanity check: rational inputs give rational outputs
for expressible features
-/
lemma rat_of_rat (e : Expressible ps) (V : ValuationSequence ps)
    (h_rat : ∀ n s, ∃ (q : ℚ), (V n s).1 = q) :
    ∃ (q : ℚ), e.vf.map V = ↑q := by
  sorry


/-- Alphabet used for encoding expressible features. -/
inductive Alphabet (ps : PrimeSentences) where
  | natA (a : PartrecToTM2.Γ')
  | sentA (a : Sentence.Alphabet ps)
  | price
  | rat
  | add
  | mul
  | max
  | safeInv


end Expressible

/- Now we work towards describing expressible features via an
`ExpressibleFeatureProgram`, which allows for more efficient encodings.
-/

/-- A single line of an `ExpressibleFeatureProgram`.
The `ℕ` are supposed to refer to earlier line numbers.
-/
inductive EFLine (ps : PrimeSentences) where
  | price : ℕ → Sentence ps → EFLine ps
  | rat : ℚ → EFLine ps
  | add : ℕ → ℕ → EFLine ps
  | mul : ℕ → ℕ → EFLine ps
  | max : ℕ → ℕ → EFLine ps
  | safeInv : ℕ → EFLine ps


namespace EFLine

/-- Which lines an `EFLine` depends on.
`⊥` represents no dependence.
`⊥` is not `0`.
We need to use `Nat.max` to avoid confusion with `EFLine.max`.
-/
def depends : (e : EFLine ps) → WithBot ℕ
  | price _ _ => ⊥
  | rat _ => ⊥
  | add a b => Nat.max a b
  | mul a b => Nat.max a b
  | max a b => Nat.max a b
  | safeInv x => x


open Expressible in
/-- Encoding an `EFLine`. -/
def encode : (e : EFLine ps) → List (@Alphabet ps)
  | price n s => Alphabet.price :: List.map Alphabet.natA (encodeNat n)
    ++ List.map Alphabet.sentA s.encode
  | rat q => Alphabet.rat :: List.map Alphabet.natA (encodeRat q)
  | add a b => Alphabet.add :: List.map Alphabet.natA (PartrecToTM2.trList [a, b])
  | mul a b => Alphabet.mul :: List.map Alphabet.natA (PartrecToTM2.trList [a, b])
  | max a b => Alphabet.max :: List.map Alphabet.natA (PartrecToTM2.trList [a, b])
  | safeInv a => Alphabet.safeInv :: List.map Alphabet.natA (encodeNat a)

/-- Sanity check: -/
lemma encode_injective : (@encode ps).Injective := by
  sorry

end EFLine

/-- Defining an `ExpressibleFeatureProgram` as a nonempty list of `EFLines`.
Also enforces that lines can only depend on earlier lines.
-/
structure ExpressibleFeatureProgram (ps : PrimeSentences) where
  lines : List (EFLine ps)
  nonempty : lines ≠ []
  depends : ∀ (i : Fin lines.length), (lines.get i).depends < i.1

namespace ExpressibleFeatureProgram

/-- Definition hole
taking the first n lines of an `ExpressibleFeatureProgram` is again a
`ExpressibleFeatureProgram`.
-/
def take (efp : ExpressibleFeatureProgram ps) (n : ℕ) (npos : 0 < n) :
    ExpressibleFeatureProgram ps := sorry

/-- Pin-down lemma -/
lemma ok_take (efp : ExpressibleFeatureProgram ps) (n : ℕ) (npos : 0 < n) :
    (efp.take n npos).lines = efp.lines.take n := by
  sorry

/-- Definition: referring to line `n`
in an `ExpressibleFeatureProgram`.
-/
def ref (efp : ExpressibleFeatureProgram ps) (n : ℕ) : ExpressibleFeatureProgram ps :=
  efp.take (n + 1) (Nat.succ_pos n)


/-- Definition hole:
Evaluating the ExpressibleFeatureProgram as an expressible feature
-/
def ef (efp : ExpressibleFeatureProgram ps) : Expressible ps :=
  sorry

/-- Pin-down lemma -/
lemma ok_ef (efp : ExpressibleFeatureProgram ps) :
    efp.ef = match (efp.lines.getLast efp.nonempty) with
    | .price n s => Expressible.price n s
    | .rat q => Expressible.rat q
    | .add a b => Expressible.add (efp.ref a).ef (efp.ref b).ef
    | .mul a b => Expressible.mul (efp.ref a).ef (efp.ref b).ef
    | .max a b => Expressible.max (efp.ref a).ef (efp.ref b).ef
    | .safeInv a => Expressible.safeInv (efp.ref a).ef := by
  sorry

/-- Sanity check: -/
lemma ef_surjective (e : Expressible ps) :
    ∃ (efp : ExpressibleFeatureProgram ps), efp.ef = e := by
  sorry

/-- The valuation feature of an `ExpressibleFeatureProgram`: -/
def vf (efp : ExpressibleFeatureProgram ps) := efp.ef.vf

/-- Encoding an `ExpressibleFeatureProgram`.
Put the length first, then put the elements of the list. -/
def encode (efp : ExpressibleFeatureProgram ps) : List (Expressible.Alphabet ps) :=
  List.map Expressible.Alphabet.natA (encodeNat efp.lines.length)
  ++ (List.map EFLine.encode efp.lines).flatten

/-- Sanity check: -/
lemma encode_injective : (@encode ps).Injective := by
  sorry

end ExpressibleFeatureProgram

end Valuation

section Trading

variable {ps : PrimeSentences}


/-- Definition: a trading strategy for day n.
We use `ExpressibleFeatureProgram` instead of `Expressible`,
to allow for better encoding.
sentences have to be distinct.
-/
structure TradingStrategy (ps : PrimeSentences) where
  day : ℕ
  k : ℕ
  sentences : Fin k → Sentence ps
  efp : Fin k → ExpressibleFeatureProgram ps
  ef_rank : ∀ l, (efp l).vf.rank ≤ day
  unique_sentences : ∀ i j, sentences i = sentences j → i = j

namespace TradingStrategy

/-- Accessing the expressible features of a `TradingStrategy` -/
def ef (T : TradingStrategy ps) (i : Fin T.k) : Expressible ps := (T.efp i).ef

/-- Definition hole:
Coefficient for a sentence. -/
noncomputable
def coeff (T : TradingStrategy ps) (s : Sentence ps) : Expressible ps :=
  sorry

/-- Pin-down lemma -/
lemma ok_coeff (T : TradingStrategy ps) (s : Sentence ps) :
    (∀ i, T.sentences i = s → T.coeff s = T.ef i)
    ∧ ((∀ i, T.sentences i ≠ s) → T.coeff s = Expressible.rat 0) := by
  sorry

/-- Definition: the cash term,
as an expressible feature.
-/
noncomputable
def cash (T : TradingStrategy ps) : Expressible ps :=
  Expressible.mul (Expressible.rat (-1))
  (Expressible.sum (fun i =>
    Expressible.mul (T.ef i) (Expressible.price T.day (T.sentences i))))

/-- Sanity check: -/
lemma coeff_rank (T : TradingStrategy ps) (s : Sentence ps) :
    (T.coeff s).vf.rank ≤ T.day := by
  sorry

/-- Sanity check: -/
lemma cash_rank (T : TradingStrategy ps) :
    T.cash.vf.rank ≤ T.day := by
  sorry

/-- Sanity check: there is a trading strategy with full rank -/
lemma exists_full_rank (n : ℕ) :
    ∃ (T : TradingStrategy ps),
    T.day = n ∧ T.cash.vf.rank = T.day
    ∧ ∃ s, (T.coeff s).vf.rank = T.day := by
  sorry

/-- Definition: holdings of a trading strategy `T`,
when interacting with a valuation sequence `V`.
Defined for sentences `s` or the cash term
(represented by the `Unit` term here).
Values can be negative.
-/
noncomputable
def holdings (T : TradingStrategy ps) (V : ValuationSequence ps) :
    Unit ⊕ Sentence ps → ℝ
  | Sum.inl _ => T.cash.vf.map V
  | Sum.inr s => (T.coeff s).vf.map V


/-- Sanity check:
holdings have finite support
-/
lemma finite_support_of_holdings (T : TradingStrategy ps)
    (V : ValuationSequence ps) :
    (T.holdings V).support.Finite := by
  sorry

/-- Sanity check (guarding against off-by-1 errors)
holdings for a day `n` trading strategy can depend on day `n` values.
If valuation sequences `V1`, `V2` differ exactly in position `n`,
then the holdings can differ, too.
-/
lemma depends_day_of_holdings (n : ℕ) (V1 V2 : ValuationSequence ps)
    (hV : ∀ k, k ≠ n ↔ V1 k = V2 k) :
    ∃ (T : TradingStrategy ps),
    T.day = n ∧ T.holdings V1 ≠ T.holdings V2 := by
  sorry

/-- Sanity check (guarding against off-by-1 errors)
holdings for a day `n` trading strategy do not depend on values after day `n`.
-/
lemma independent_of_after_day (T : TradingStrategy ps) (V1 V2 : ValuationSequence ps)
    (hV : ∀ k, k ≤ T.day → V1 k = V2 k) :
    T.holdings V1 = T.holdings V2 := by
  sorry

/-- Encode a trading strategy
We use the same alphabet as in `Expressible`.
We start with encoding `T.k`.
Then we list the `T.k` sentences.
Then we list the `T.k` expressible feature programs.
Then we list the trading day.
-/
def encode (T : TradingStrategy ps) : List (Expressible.Alphabet ps) :=
  (List.map Expressible.Alphabet.natA (encodeNat T.k))
  ++ (List.ofFn (fun i => List.map Expressible.Alphabet.sentA (T.sentences i).encode)).flatten
  ++ (List.ofFn (fun i => (T.efp i).encode)).flatten
  ++ (List.map Expressible.Alphabet.natA (encodeNat T.day))

/-- Sanity check: encoding is injective -/
lemma encode_injective : (@encode ps).Injective := by
  sorry


end TradingStrategy

/-- Definition (trader): -/
def Trader (ps : PrimeSentences) := {f : ℕ → TradingStrategy ps // ∀ n, (f n).day = n }

namespace Trader

/-- Definition: a trader is efficiently computable -/
def IsEC (T : Trader ps) : Prop :=
  IsEfficientlyComputable TradingStrategy.encode T.val

/-- Definition (value of holdings of a trader):
Uses `∑ᶠ`, which returns `0` if infinitely many entries are nonzero.
In our case we have finite support, so it works as intended.
-/
noncomputable
def worldVal (T : Trader ps) (W : World ps) (n : ℕ) (V : ValuationSequence ps) : ℝ :=
  (∑ᶠ s, (W s).toNat * ∑ i ∈ Finset.range (n + 1), ((T.val i).coeff s).vf.map V)
  + ∑ i ∈ Finset.range (n + 1), (T.val i).cash.vf.map V

/-- Definition (net holdings of a trader):
Just the sum of the holdings of the trading strategies.
Note that `Finset.sum` is automatically defined for `Unit ⊕ Sentence → ℝ`.
-/
noncomputable
def netHoldings (T : Trader ps) (n : ℕ) (V : ValuationSequence ps) :
    Unit ⊕ Sentence ps → ℝ :=
  ∑ (i : Fin (n + 1)), (T.val i.1).holdings V

/-- Sanity check: -/
lemma finite_support_of_netHoldings (T : Trader ps) (n : ℕ)
    (V : ValuationSequence ps) :
    (T.netHoldings n V).support.Finite := by
  sorry

/-- Definition (value of a holding):
Discards sentences that are false under world `W`.
Needs that the holding has finite support.
-/
def worldValOfHoldings (W : World ps) (holding : Unit ⊕ Sentence ps → ℝ)
    [Fintype ↑holding.support] : ℝ :=
  holding.support.toFinset.sum (fun x => match x with
    | Sum.inl y => holding (Sum.inl y)
    | Sum.inr s => if (W s) then holding (Sum.inr s) else 0
  )

/-- Sanity check:
world value is monotone in holdings
-/
lemma worldValOfHoldings_mono (W : World ps) (h1 h2)
    (h12 : h1 ≤ h2)
    [Fintype h1.support] [Fintype h2.support] :
    worldValOfHoldings W h1 ≤ worldValOfHoldings W h2 := by
  sorry

/-- Sanity check:
Formula for `T.worldVal W n V`.
-/
lemma ok_worldVal (T : Trader ps) (W : World ps) (n : ℕ) (V : ValuationSequence ps) :
    T.worldVal W n V =
    @worldValOfHoldings ps W (T.netHoldings n V)
    (T.finite_support_of_netHoldings n V).fintype := by
  sorry


/-- Sanity check
If a trader buys 1 share of various true things every day, then worldVal ≥ 0
-/
lemma nonneg_of_buy_true (T : Trader ps) (W : World ps)
    (h_ef_1 : ∀ i, ∀ j, (T.val i).ef j = Expressible.rat 1)
    (h_true : ∀ i, ∀ j, W ((T.val i).sentences j) = true) :
    ∀ n V, T.worldVal W n V ≥ 0 := by
  sorry

/-- Sanity check
If a trader buys 1 share of various false things every day, then worldVal ≤ 0
-/
lemma nonpos_of_buy_false (T : Trader ps) (W : World ps)
    (h_ef_1 : ∀ i, ∀ j, (T.val i).ef j = Expressible.rat 1)
    (h_false : ∀ i, ∀ j, W ((T.val i).sentences j) = false) :
    ∀ n V, T.worldVal W n V ≤ 0 := by
  sorry

/-- Sanity check:
given a trader, there exists an opposite trader.
-/
lemma exists_opposite_trader (T1 : Trader ps) :
    ∃ (T2 : Trader ps), ∀ W n V, T1.worldVal W n V + T2.worldVal W n V = 0 := by
  sorry

/-- Sanity check:
If there ever exists a sentence whose value is strictly between 0 and 1, then
there is a trader for every profit
-/
lemma exists_profitable_trader_of_Ioo (n : ℕ) W
    (V : ValuationSequence ps) s
    (hV : (V n s).1 ≠ 0 ∧ (V n s).1 ≠ 1) (profit : ℚ) :
    ∃ (T : Trader ps), T.worldVal W n V = ↑profit := by
  sorry

/-- Definition (trader exploits):
-/
def Exploits (T : Trader ps) (V : ValuationSequence ps)
    (D : DeductiveProcess ps) : Prop :=
  let A := {x | ∃ n W, x = T.worldVal W n V ∧ W ∈ PC (D.toSet n)}
  BddBelow A ∧ ¬BddAbove A


/-- Sanity check:
given a nonempty deductive process, there exists a valuation sequence
and an efficiently computable trader that exploits,
provided at least one world is consistent with all statements
from the deductive process.
This sanity check is also to ensure that exploitation with
an efficiently computable trader is possible in principle.
-/
lemma exists_trader_exploits (D : DeductiveProcess ps)
    (h1 : (D.toSet 0) ≠ ∅)
    (h2 : ∃ W, W ∈ PC (⋃ (k : ℕ), D.toSet k)) :
    ∃ (T : Trader ps) (V : ValuationSequence ps),
    T.Exploits V D ∧ T.IsEC := by
  sorry

end Trader

end Trading

section ComputableSupport

variable {ps : PrimeSentences}

/-- Check whether an encoded sentence is valid for a PrimeSentence
-/
def IsValidEncoding (l : List ps.Alphabet) : Prop :=
  ∃ (s : ps.PS), ps.encode s = l

open Classical in
/-- Encoding a proposition -/
noncomputable
def encodeProp (p : Prop) : List Unit :=
  if p then [.unit] else []

/-- Sanity check: -/
lemma encodeProp_injective : encodeProp.Injective := by
  sorry

/-- Definition: whether the validity of an encoding
of prime sentences can be decided. -/
def HasDecidableEncoding : Prop :=
  Nonempty <| TM2Computable id encodeProp (@IsValidEncoding ps)

/-- Definition:
the support of `P.val n` is computable from `n`,
where the support is a concrete finite list.
-/
def HasComputableSupport (P : Market ps) : Prop :=
  ∃ (supp : ℕ → List (Sentence ps)),
  (∀ n, ∀ x, P.val n x > 0 ↔ x ∈ supp n) ∧
  IsComputableSequence encodeSentenceList supp

/-- Sanity check: -/
lemma isBeliefState_of_hasComputableSupport (P : Market ps) (h1 : HasComputableSupport P) :
    ∀ n, IsBeliefState (P.val n) := by
  sorry

end ComputableSupport

section MainResult

variable {ps : PrimeSentences}

/-- Definition:
A market is a logical inductor if it cannot be exploited by an e.c. trader `T`
relative to a deductive process `D`.
-/
def IsLogicalInductor (P : Market ps) (D : DeductiveProcess ps) : Prop :=
  ¬ ∃ (T : Trader ps), T.IsEC ∧ T.Exploits P.valSequence D

/-- Theorem: There exists a logical inductor.
-/
theorem exists_logical_inductor (D : DeductiveProcess ps) :
    ∃ (P : Market ps), (∀ n, IsBeliefState (P.val n)) ∧
    IsLogicalInductor P D := by
  sorry

/-- Theorem:
This gives a stronger computability result: The logical inductor also has computable support.
But it also requires that it can be computed whether an encoding of prime sentences is valid.
Because of `isBeliefState_of_hasComputableSupport`,
the same market can be chosen as in `exists_logical_inductor`.
-/
theorem exists_LI_with_ComputableSupport (D : DeductiveProcess ps)
    (h : @HasDecidableEncoding ps) :
    ∃ (P : Market ps), HasComputableSupport P ∧
    IsLogicalInductor P D := by
  sorry

end MainResult


end LogicalInduction
