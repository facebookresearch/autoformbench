import Mathlib

set_option autoImplicit false

noncomputable section

namespace Autoform_Introduction_to_the_Theory_of_Computation_computation_coISO_mem_IP





















abbrev BinaryString : Type := List Bool


abbrev Language : Type := Set BinaryString





def encodeUnaryNat (n : Nat) : BinaryString :=
  List.replicate n true ++ [false]


def readUnaryNat : BinaryString → Option (Nat × BinaryString)
  | [] => none
  | false :: xs => some (0, xs)
  | true :: xs =>
      match readUnaryNat xs with
      | none => none
      | some (n, rest) => some (n + 1, rest)








structure BoolSimpleGraph (n : Nat) where
  adj : Fin n → Fin n → Bool
  symm : ∀ i j : Fin n, adj i j = adj j i
  loopless : ∀ i : Fin n, adj i i = false

namespace BoolSimpleGraph







def toSimpleGraph {n : Nat} (G : BoolSimpleGraph n) : SimpleGraph (Fin n) :=
  SimpleGraph.mk'
    ⟨G.adj, by
      constructor
      · intro i j
        exact G.symm i j
      · intro i
        simp [G.loopless i]⟩


end BoolSimpleGraph


def bitsToAdj {n : Nat} (bits : BinaryString) (i j : Fin n) : Bool :=
  bits.getD (i.val * n + j.val) false


def IsGraphBits (n : Nat) (bits : BinaryString) : Prop :=
  bits.length = n * n ∧
    (∀ i : Fin n, bitsToAdj bits i i = false) ∧
    (∀ i j : Fin n, bitsToAdj bits i j = bitsToAdj bits j i)


noncomputable def decodeBoolSimpleGraph
    (n : Nat) (bits : BinaryString) : Option (BoolSimpleGraph n) := by
  classical
  exact
    if h : IsGraphBits n bits then
      some
        { adj := bitsToAdj bits
          symm := h.2.2
          loopless := h.2.1 }
    else
      none







structure GraphPair where
  n : Nat
  G : BoolSimpleGraph n
  H : BoolSimpleGraph n

namespace GraphPair







def Isomorphic (p : GraphPair) : Prop :=
  Nonempty
    (BoolSimpleGraph.toSimpleGraph p.G ≃g
      BoolSimpleGraph.toSimpleGraph p.H)

end GraphPair










noncomputable def decodeGraphPair (w : BinaryString) : Option GraphPair := by
  classical
  exact
    match readUnaryNat w with
    | none => none
    | some (n, rest) =>
        let graphSize : Nat := n * n
        let gBits : BinaryString := rest.take graphSize
        let hBits : BinaryString := (rest.drop graphSize).take graphSize
        let extra : BinaryString := rest.drop (2 * graphSize)
        if extra = [] then
          match decodeBoolSimpleGraph n gBits, decodeBoolSimpleGraph n hBits with
          | some G, some H => some { n := n, G := G, H := H }
          | _, _ => none
        else
          none







def ISO : Language :=
  { w | ∃ p : GraphPair, decodeGraphPair w = some p ∧ GraphPair.Isomorphic p }


def coISO : Language :=
  ISOᶜ







def PolynomiallyBounded (f : Nat → Nat) : Prop :=
  ∃ p : Polynomial Nat, ∀ n : Nat, f n ≤ Polynomial.eval n p







def PolyTimeNatFunction (f : Nat → Nat) : Prop :=
  Nonempty
    (Turing.TM2ComputableInPolyTime
      Computability.encodeNat Computability.encodeNat f)





def PolyTimeBinaryFunction (f : BinaryString → BinaryString) : Prop :=
  Nonempty
    (Turing.TM2ComputableInPolyTime
      (fun x : BinaryString => x) (fun x : BinaryString => x) f)


def PolyTimeBoolFunction (f : BinaryString → Bool) : Prop :=
  Nonempty
    (Turing.TM2ComputableInPolyTime
      (fun x : BinaryString => x) Computability.encodeBool f)


abbrev Transcript : Type :=
  List (BinaryString × BinaryString)


abbrev RandomTape (n : Nat) : Type :=
  Fin n → Bool


def randomTapeToList {n : Nat} (r : RandomTape n) : BinaryString :=
  List.ofFn r


def encodeBlock (xs : BinaryString) : BinaryString :=
  encodeUnaryNat xs.length ++ xs


def encodeTranscriptMessage (m : BinaryString × BinaryString) : BinaryString :=
  encodeBlock m.1 ++ encodeBlock m.2


def encodeTranscript (t : Transcript) : BinaryString :=
  encodeUnaryNat t.length ++ (t.map encodeTranscriptMessage).flatten








def encodeVerifierQuery
    (w : BinaryString) (r : BinaryString) (t : Transcript) : BinaryString :=
  encodeBlock w ++ encodeBlock r ++ encodeTranscript t









structure Prover where
  reply : BinaryString → Transcript → BinaryString → BinaryString











structure InteractiveVerifier where
  numRounds : Nat → Nat
  randomLength : Nat → Nat
  proverMessageLength : Nat → Nat
  verifierMessageLength : Nat → Nat

  nextMessage : BinaryString → BinaryString
  accept : BinaryString → Bool

  numRounds_polyBounded : PolynomiallyBounded numRounds
  randomLength_polyBounded : PolynomiallyBounded randomLength
  proverMessageLength_polyBounded : PolynomiallyBounded proverMessageLength
  verifierMessageLength_polyBounded : PolynomiallyBounded verifierMessageLength

  numRounds_polyTime : PolyTimeNatFunction numRounds
  randomLength_polyTime : PolyTimeNatFunction randomLength
  proverMessageLength_polyTime : PolyTimeNatFunction proverMessageLength
  verifierMessageLength_polyTime : PolyTimeNatFunction verifierMessageLength

  nextMessage_polyTime : PolyTimeBinaryFunction nextMessage
  accept_polyTime : PolyTimeBoolFunction accept

  nextMessage_length_bound :
    ∀ (w r : BinaryString) (t : Transcript),
      (nextMessage (encodeVerifierQuery w r t)).length ≤
        verifierMessageLength w.length

namespace InteractiveVerifier







def runTranscript
    (V : InteractiveVerifier) (P : Prover) (w : BinaryString)
    {m : Nat} (r : RandomTape m) : Nat → Transcript
  | 0 => []
  | k + 1 =>
      let t := runTranscript V P w r k
      let vmsg := V.nextMessage (encodeVerifierQuery w (randomTapeToList r) t)
      let pmsg := (P.reply w t vmsg).take (V.proverMessageLength w.length)
      t ++ [(vmsg, pmsg)]


def accepts
    (V : InteractiveVerifier) (P : Prover) (w : BinaryString)
    (r : RandomTape (V.randomLength w.length)) : Bool :=
  let t := V.runTranscript P w r (V.numRounds w.length)
  V.accept (encodeVerifierQuery w (randomTapeToList r) t)







noncomputable def acceptanceProbability
    (V : InteractiveVerifier) (P : Prover) (w : BinaryString) : ℚ := by
  classical
  exact
    (((Finset.univ.filter
        (fun r : RandomTape (V.randomLength w.length) =>
          V.accepts P w r = true)).card : Nat) : ℚ) /
      ((Fintype.card (RandomTape (V.randomLength w.length)) : Nat) : ℚ)

end InteractiveVerifier












def HasInteractiveProof (L : Language) : Prop :=
  ∃ V : InteractiveVerifier,
    (∀ w : BinaryString, w ∈ L →
      ∃ P : Prover,
        ((2 : ℚ) / 3) ≤ V.acceptanceProbability P w) ∧
    (∀ w : BinaryString, w ∉ L →
      ∀ P : Prover,
        V.acceptanceProbability P w ≤ ((1 : ℚ) / 3))


def IP : Set Language :=
  { L | HasInteractiveProof L }



end Autoform_Introduction_to_the_Theory_of_Computation_computation_coISO_mem_IP
