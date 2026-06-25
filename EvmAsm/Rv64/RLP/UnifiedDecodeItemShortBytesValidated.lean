/-
  EvmAsm.Rv64.RLP.UnifiedDecodeItemShortBytesValidated

  Phase B.1 of issue #9373 — a VALIDATING shortBytes RLP single-item decoder over UNTRUSTED input.
  Unlike the valid-path decoder (which assumes the input is a well-formed encoding), this is a
  2-exit `cpsBranchWithin`: the SUCCESS exit carries `⌜decode (pfx::rest) = some (.bytes data, rest')⌝`
  and the FAIL exit carries `⌜decode (pfx::rest) = none⌝`, with NO validity hypotheses on the input.

  The untrusted-length contract: register `x15` holds the available byte count `L = (pfx::rest).length`
  (the codegen K20 model). The decoder runs the valid-path shortBytes handler (which computes
  `x11 = payloadLen = pfx-0x80`, `x13 = payloadPtr`), then a single `BLTU x11, x15` bound check:
  taken (`payloadLen < L`) ⟺ the payload fits ⟺ `takeBytes rest payloadLen = some …` ⟺ SUCCESS;
  fall-through (`payloadLen ≥ L`) ⟺ truncated ⟺ `takeBytes = none` ⟺ FAIL.

  This first unit covers the non-singleton case (`payloadLen ≠ 1`), for which the RLP single-byte
  canonical check is vacuous; the `payloadLen = 1` (prefix `0x81`) singleton-canonical sub-branch
  (`LBU`/`ANDI 0x80`/`BNE`, reusing `byte_zext_and_0x80_eq_zero_imp_lt`) is the follow-up that drops
  the `hns` hypothesis. The success/fail distinction is exposed as two exit PCs (a thin wrapper sets
  `a0`); the verified content is the `⌜decode = some/none⌝` propositions.
-/

import EvmAsm.Rv64.RLP.Phase1E2FullPath
import EvmAsm.Rv64.MemRegion
import EvmAsm.EL.RLP.ByteStringDecodeBridge

namespace EvmAsm.Rv64.RLP

open EvmAsm.Rv64
open EvmAsm.EL.RLP
open EvmAsm.EL.RLP.ByteStringDecodeBridge
open EvmAsm.Rv64.Tactics

set_option maxRecDepth 8000 in
/-- The bound-check `BLTU x11, x15` taken condition `ult (ofNat len) (ofNat L)` is exactly the
    Nat fact `len < L`, given both fit in 64 bits. -/
private theorem ult_ofNat_len (len L : Nat) (hlen : len < 2 ^ 64) (hL : L < 2 ^ 64) :
    BitVec.ult (BitVec.ofNat 64 len) (BitVec.ofNat 64 L) ↔ len < L := by
  rw [BitVec.ult_eq_decide]
  simp only [BitVec.toNat_ofNat, Nat.mod_eq_of_lt hlen, Nat.mod_eq_of_lt hL, decide_eq_true_eq]

set_option maxRecDepth 8000 in
/-- **Validating shortBytes single-item decoder (non-singleton), at offset 0.** From an untrusted
    `bytesRegion regionBase (pfx::rest)` with `x15 = (pfx::rest).length`, runs the valid-path
    shortBytes handler then a `BLTU x11, x15` bound check. SUCCESS (taken) ⇒ `decode (pfx::rest)`
    yields the byte string; FAIL (fall) ⇒ `decode (pfx::rest) = none`. No validity hypotheses. -/
theorem rlp_decode_shortBytes_validated
    (pfx : Byte) (rest : List Byte)
    (v10 v11Old v12Old v14Old : Word)
    (regionBase : Word)
    (off1 off2 succOff : BitVec 13) (base e2_target : Word)
    (h_class : classifyPrefix pfx = .shortBytes)
    (hns : rlpPrefixShortBytesPayloadLen pfx ≠ 1)
    (hover : regionBase.toNat + (pfx :: rest).length < 2 ^ 64)
    (htarget : (base + 8 + 4) + signExtend13 off2 = e2_target)
    (hd_phase3 : ((rlp_phase1_step_code 0x80 off1 base).union
                    (rlp_phase1_step_code 0xB8 off2 (base + 8))).Disjoint
                 (CodeReq.ofProg e2_target rlp_phase3_short_string_prog))
    (hd_bltu : (((rlp_phase1_step_code 0x80 off1 base).union
                    (rlp_phase1_step_code 0xB8 off2 (base + 8))).union
                 (CodeReq.ofProg e2_target rlp_phase3_short_string_prog)).Disjoint
               (CodeReq.singleton (e2_target + 8) (.BLTU .x11 .x15 succOff))) :
    cpsBranchWithin 7 base
      ((((rlp_phase1_step_code 0x80 off1 base).union
          (rlp_phase1_step_code 0xB8 off2 (base + 8))).union
         (CodeReq.ofProg e2_target rlp_phase3_short_string_prog)).union
        (CodeReq.singleton (e2_target + 8) (.BLTU .x11 .x15 succOff)))
      ((.x5 ↦ᵣ pfx.zeroExtend 64) ** (.x0 ↦ᵣ (0 : Word)) ** (.x10 ↦ᵣ v10) **
        (.x11 ↦ᵣ v11Old) ** (.x12 ↦ᵣ v12Old) ** (.x13 ↦ᵣ regionBase) ** (.x14 ↦ᵣ v14Old) **
        (.x15 ↦ᵣ (BitVec.ofNat 64 (pfx :: rest).length)) ** bytesRegion regionBase (pfx :: rest))
      -- SUCCESS (taken: payloadLen < L)
      ((e2_target + 8) + signExtend13 succOff)
        ((.x5 ↦ᵣ pfx.zeroExtend 64) ** (.x0 ↦ᵣ (0 : Word)) **
          (.x10 ↦ᵣ ((0 : Word) + signExtend12 (0xB8 : BitVec 12))) **
          (.x11 ↦ᵣ (BitVec.ofNat 64 (rlpPrefixShortBytesPayloadLen pfx))) **
          (.x12 ↦ᵣ v12Old) ** (.x13 ↦ᵣ (regionBase + signExtend12 (1 : BitVec 12))) **
          (.x14 ↦ᵣ v14Old) ** (.x15 ↦ᵣ (BitVec.ofNat 64 (pfx :: rest).length)) **
          bytesRegion regionBase (pfx :: rest) **
          ⌜decode (pfx :: rest)
            = some (.bytes (rest.take (rlpPrefixShortBytesPayloadLen pfx)),
                    rest.drop (rlpPrefixShortBytesPayloadLen pfx))⌝)
      -- FAIL (fall: payloadLen ≥ L)
      (e2_target + 12)
        ((.x5 ↦ᵣ pfx.zeroExtend 64) ** (.x0 ↦ᵣ (0 : Word)) **
          (.x10 ↦ᵣ ((0 : Word) + signExtend12 (0xB8 : BitVec 12))) **
          (.x11 ↦ᵣ (BitVec.ofNat 64 (rlpPrefixShortBytesPayloadLen pfx))) **
          (.x12 ↦ᵣ v12Old) ** (.x13 ↦ᵣ (regionBase + signExtend12 (1 : BitVec 12))) **
          (.x14 ↦ᵣ v14Old) ** (.x15 ↦ᵣ (BitVec.ofNat 64 (pfx :: rest).length)) **
          bytesRegion regionBase (pfx :: rest) **
          ⌜decode (pfx :: rest) = none⌝) := by
  -- payloadLen ≤ 55 ⇒ both fit in 64 bits; abbreviate len/L.
  set len := rlpPrefixShortBytesPayloadLen pfx with hlen_def
  have hlen55 : len ≤ 55 := rlpPrefixShortBytesPayloadLen_le_55_of_class h_class
  have hL_lt : (pfx :: rest).length < 2 ^ 64 := by omega
  have hlen_lt : len < 2 ^ 64 := by omega
  -- The two semantic bridges (pure): the runtime bound-check condition ⇒ the decode verdict.
  have hsome : BitVec.ult (BitVec.ofNat 64 len) (BitVec.ofNat 64 (pfx :: rest).length) →
      decode (pfx :: rest) = some (.bytes (rest.take len), rest.drop len) := by
    intro hult
    have hlt : len < (pfx :: rest).length := (ult_ofNat_len len _ hlen_lt hL_lt).mp hult
    have hle : len ≤ rest.length := by simp only [List.length_cons] at hlt; omega
    have htake : takeBytes rest len = some (rest.take len, rest.drop len) := by
      unfold takeBytes; rw [if_pos (by omega)]
    -- canonical condition is vacuous: `rest.take len` is not a singleton (len ≠ 1).
    have hlen_take : (rest.take len).length = len := by
      rw [List.length_take, Nat.min_eq_left hle]
    have hcanon : (match rest.take len with | [b] => ¬ b.toNat < 0x80 | _ => True) := by
      split
      · exfalso; rename_i b heq; rw [heq] at hlen_take; simp at hlen_take; omega
      · trivial
    rw [decode_cons_eq_decodeAux_fuel,
        show 2 * rest.length + 2 = (2 * rest.length + 1) + 1 from rfl,
        decodeAux_cons_shortBytes_eq_some_iff (2 * rest.length + 1) pfx rest h_class
          (rest.take len) (rest.drop len)]
    exact ⟨rest.take len, htake, rfl, hcanon⟩
  have hnone : ¬ BitVec.ult (BitVec.ofNat 64 len) (BitVec.ofNat 64 (pfx :: rest).length) →
      decode (pfx :: rest) = none := by
    intro hnu
    have hge : ¬ len < (pfx :: rest).length := fun hlt => hnu ((ult_ofNat_len len _ hlen_lt hL_lt).mpr hlt)
    have hgt : rest.length < len := by simp only [List.length_cons] at hge; omega
    have htake : takeBytes rest len = none := by unfold takeBytes; rw [if_neg (by omega)]
    rw [decode_cons_eq_decodeAux_fuel,
        show 2 * rest.length + 2 = (2 * rest.length + 1) + 1 from rfl]
    exact decodeAux_cons_shortBytes_eq_none_of_takeBytes_none (2 * rest.length + 1) pfx rest h_class htake
  -- The valid-path handler (6 steps, base → e2_target+8), framed with x12/x14/x15/region.
  have handler := rlp_phase1_e2_full_path_payload_len_of_class_spec_within
    pfx v10 v11Old regionBase off1 off2 base e2_target htarget h_class hd_phase3
  have handlerF := cpsTripleWithin_frameR
    ((.x12 ↦ᵣ v12Old) ** (.x14 ↦ᵣ v14Old) **
     (.x15 ↦ᵣ (BitVec.ofNat 64 (pfx :: rest).length)) ** bytesRegion regionBase (pfx :: rest))
    (by exact pcFree_sepConj pcFree_regIs (pcFree_sepConj pcFree_regIs
      (pcFree_sepConj pcFree_regIs (bytesRegion_pcFree _ _)))) handler
  -- The bound check `BLTU x11, x15` (1 step) at e2_target+8, framed with the rest of the state.
  have bltuF := cpsBranchWithin_frameR
    ((.x5 ↦ᵣ pfx.zeroExtend 64) ** (.x0 ↦ᵣ (0 : Word)) **
      (.x10 ↦ᵣ ((0 : Word) + signExtend12 (0xB8 : BitVec 12))) ** (.x12 ↦ᵣ v12Old) **
      (.x13 ↦ᵣ (regionBase + signExtend12 (1 : BitVec 12))) ** (.x14 ↦ᵣ v14Old) **
      bytesRegion regionBase (pfx :: rest))
    (by exact pcFree_sepConj pcFree_regIs (pcFree_sepConj pcFree_regIs (pcFree_sepConj pcFree_regIs
      (pcFree_sepConj pcFree_regIs (pcFree_sepConj pcFree_regIs (pcFree_sepConj pcFree_regIs
        (bytesRegion_pcFree _ _)))))))
    (bltu_spec_gen_within .x11 .x15 succOff (BitVec.ofNat 64 len)
      (BitVec.ofNat 64 (pfx :: rest).length) (e2_target + 8))
  -- Reshape the handler's POST to exactly the branch's PRE (target pinned ⇒ xperm is concrete).
  have handlerF' := cpsTripleWithin_weaken (fun _ h => h) (fun _ hp => by xperm_hyp hp)
    (Q' := (((.x11 ↦ᵣ (BitVec.ofNat 64 len)) **
              (.x15 ↦ᵣ (BitVec.ofNat 64 (pfx :: rest).length))) **
            ((.x5 ↦ᵣ pfx.zeroExtend 64) ** (.x0 ↦ᵣ (0 : Word)) **
              (.x10 ↦ᵣ ((0 : Word) + signExtend12 (0xB8 : BitVec 12))) ** (.x12 ↦ᵣ v12Old) **
              (.x13 ↦ᵣ (regionBase + signExtend12 (1 : BitVec 12))) ** (.x14 ↦ᵣ v14Old) **
              bytesRegion regionBase (pfx :: rest)))) handlerF
  have composed := cpsTripleWithin_seq_cpsBranchWithin hd_bltu handlerF' bltuF
  rw [show (e2_target + 8 : Word) + 4 = e2_target + 12 from by bv_omega] at composed
  -- Weaken to the goal: reshape the PRE (xperm) and the two posts to the decode verdicts.
  refine cpsBranchWithin_weaken (fun _ hp => by xperm_hyp hp) ?succ ?fail composed
  case succ =>
    intro h hp
    have hp' : (((.x5 ↦ᵣ pfx.zeroExtend 64) ** (.x0 ↦ᵣ (0 : Word)) **
        (.x10 ↦ᵣ ((0 : Word) + signExtend12 (0xB8 : BitVec 12))) **
        (.x11 ↦ᵣ (BitVec.ofNat 64 len)) ** (.x12 ↦ᵣ v12Old) **
        (.x13 ↦ᵣ (regionBase + signExtend12 (1 : BitVec 12))) ** (.x14 ↦ᵣ v14Old) **
        (.x15 ↦ᵣ (BitVec.ofNat 64 (pfx :: rest).length)) ** bytesRegion regionBase (pfx :: rest)) **
        ⌜BitVec.ult (BitVec.ofNat 64 len) (BitVec.ofNat 64 (pfx :: rest).length)⌝) h := by
      xperm_hyp hp
    obtain ⟨hregs, hult⟩ := (sepConj_pure_right h).1 hp'
    have hgoal := (sepConj_pure_right h).2 ⟨hregs, hsome hult⟩
    xperm_hyp hgoal
  case fail =>
    intro h hp
    have hp' : (((.x5 ↦ᵣ pfx.zeroExtend 64) ** (.x0 ↦ᵣ (0 : Word)) **
        (.x10 ↦ᵣ ((0 : Word) + signExtend12 (0xB8 : BitVec 12))) **
        (.x11 ↦ᵣ (BitVec.ofNat 64 len)) ** (.x12 ↦ᵣ v12Old) **
        (.x13 ↦ᵣ (regionBase + signExtend12 (1 : BitVec 12))) ** (.x14 ↦ᵣ v14Old) **
        (.x15 ↦ᵣ (BitVec.ofNat 64 (pfx :: rest).length)) ** bytesRegion regionBase (pfx :: rest)) **
        ⌜¬ BitVec.ult (BitVec.ofNat 64 len) (BitVec.ofNat 64 (pfx :: rest).length)⌝) h := by
      xperm_hyp hp
    obtain ⟨hregs, hnu⟩ := (sepConj_pure_right h).1 hp'
    have hgoal := (sepConj_pure_right h).2 ⟨hregs, hnone hnu⟩
    xperm_hyp hgoal

/-- `signExtend12 (-(1 : BitVec 12)) = -(1 : Word)` (the `ADDI x12, x11, -1` decrement). -/
theorem se12_neg1 : signExtend12 (-(1 : BitVec 12)) = (-1 : Word) := by decide

/-- `signExtend12 0x80 = 0x80` (the `ANDI x12, x12, 0x80` mask is positive). -/
theorem se12_0x80 : signExtend12 (0x80 : BitVec 12) = (0x80 : Word) := by decide

/-- A byte whose bit 7 is clear (`& 0x80 = 0`) is `< 0x80`. Exhaustive `decide` over 256 bytes. -/
theorem byte_and_0x80_zero_imp_lt (b : Byte)
    (h : (b.zeroExtend 64) &&& (0x80 : Word) = 0) : b.toNat < 0x80 := by
  revert h; revert b; decide

/-- Converse: a byte `< 0x80` has bit 7 clear, so masking with `0x80` yields `0`.
    Proved by exhaustive `decide` over the 256 byte values. -/
theorem byte_lt_0x80_imp_zext_and_0x80_eq_zero (b : Byte)
    (hlt : b.toNat < 0x80) : (b.zeroExtend 64) &&& (0x80 : Word) = 0 := by
  revert hlt; revert b; decide

/-- **Singleton canonical byte-check sub-branch** (the `LBU ⨾ ANDI 0x80 ⨟ BEQ` tail). Reads the
    single payload byte at `regionBase + 1` (the shortBytes singleton payload pointer), masks bit 7,
    and branches: TAKEN (`BEQ`, byte `< 0x80`) ⇒ non-canonical ⇒ the FAIL exit; FALL (byte `≥ 0x80`)
    ⇒ canonical ⇒ the success-ward exit. Used by the full validating shortBytes decoder for the
    `payloadLen = 1` case. -/
theorem shortBytes_canon_byteChk_within
    (regionBase v12 : Word) (bs : List Byte) (base : Word) (failOff : BitVec 13)
    (halign : regionBase.toNat % 8 = 0) (h1lt : 1 < bs.length)
    (_hover : regionBase.toNat + bs.length < 2 ^ 64)
    (hvalid1 : isValidByteAccess (regionBase + BitVec.ofNat 64 1) = true)
    (hd1 : (CodeReq.singleton base (.LBU .x12 .x13 0)).Disjoint
            (CodeReq.singleton (base + 4) (.ANDI .x12 .x12 0x80)))
    (hd2 : ((CodeReq.singleton base (.LBU .x12 .x13 0)).union
              (CodeReq.singleton (base + 4) (.ANDI .x12 .x12 0x80))).Disjoint
            (CodeReq.singleton (base + 8) (.BEQ .x12 .x0 failOff))) :
    cpsBranchWithin 3 base
      (((CodeReq.singleton base (.LBU .x12 .x13 0)).union
          (CodeReq.singleton (base + 4) (.ANDI .x12 .x12 0x80))).union
        (CodeReq.singleton (base + 8) (.BEQ .x12 .x0 failOff)))
      ((.x13 ↦ᵣ (regionBase + BitVec.ofNat 64 1)) ** (.x12 ↦ᵣ v12) ** (.x0 ↦ᵣ (0 : Word)) **
        bytesRegion regionBase bs)
      -- TAKEN (byte < 0x80): non-canonical → FAIL
      ((base + 8) + signExtend13 failOff)
        ((.x13 ↦ᵣ (regionBase + BitVec.ofNat 64 1)) **
          (.x12 ↦ᵣ ((bs[1]'h1lt).zeroExtend 64 &&& (0x80 : Word))) ** (.x0 ↦ᵣ (0 : Word)) **
          bytesRegion regionBase bs ** ⌜(bs[1]'h1lt).toNat < 0x80⌝)
      -- FALL (byte ≥ 0x80): canonical → success-ward
      (base + 12)
        ((.x13 ↦ᵣ (regionBase + BitVec.ofNat 64 1)) **
          (.x12 ↦ᵣ ((bs[1]'h1lt).zeroExtend 64 &&& (0x80 : Word))) ** (.x0 ↦ᵣ (0 : Word)) **
          bytesRegion regionBase bs ** ⌜¬ (bs[1]'h1lt).toNat < 0x80⌝) := by
  -- LBU x12, x13, 0 (base → base+4): x12 := bs[1].
  have lbuS : cpsTripleWithin 1 base (base + 4)
      (CodeReq.singleton base (.LBU .x12 .x13 0))
      ((.x13 ↦ᵣ (regionBase + BitVec.ofNat 64 1)) ** (.x12 ↦ᵣ v12) ** (.x0 ↦ᵣ (0 : Word)) **
        bytesRegion regionBase bs)
      ((.x13 ↦ᵣ (regionBase + BitVec.ofNat 64 1)) ** (.x12 ↦ᵣ ((bs[1]'h1lt).zeroExtend 64)) **
        (.x0 ↦ᵣ (0 : Word)) ** bytesRegion regionBase bs) :=
    cpsTripleWithin_weaken (fun _ hp => by xperm_hyp hp) (fun _ hp => by xperm_hyp hp)
      (cpsTripleWithin_frameR (.x0 ↦ᵣ (0 : Word)) (by pcFree)
        (bytesRegion_lbu_within .x12 .x13 regionBase v12 base bs 1 (by nofun)
          halign h1lt (by omega) hvalid1))
  -- ANDI x12, x12, 0x80 (base+4 → base+8): x12 := bs[1] &&& 0x80.
  have andiS : cpsTripleWithin 1 (base + 4) (base + 8)
      (CodeReq.singleton (base + 4) (.ANDI .x12 .x12 0x80))
      ((.x13 ↦ᵣ (regionBase + BitVec.ofNat 64 1)) ** (.x12 ↦ᵣ ((bs[1]'h1lt).zeroExtend 64)) **
        (.x0 ↦ᵣ (0 : Word)) ** bytesRegion regionBase bs)
      ((.x13 ↦ᵣ (regionBase + BitVec.ofNat 64 1)) **
        (.x12 ↦ᵣ ((bs[1]'h1lt).zeroExtend 64 &&& (0x80 : Word))) ** (.x0 ↦ᵣ (0 : Word)) **
        bytesRegion regionBase bs) := by
    have andi_raw := andi_spec_gen_same_within .x12 ((bs[1]'h1lt).zeroExtend 64) 0x80 (base + 4) (by nofun)
    rw [se12_0x80, show (base + 4 : Word) + 4 = base + 8 from by bv_omega] at andi_raw
    exact cpsTripleWithin_weaken (fun _ hp => by xperm_hyp hp) (fun _ hp => by xperm_hyp hp)
      (cpsTripleWithin_frameR
        ((.x13 ↦ᵣ (regionBase + BitVec.ofNat 64 1)) ** (.x0 ↦ᵣ (0 : Word)) ** bytesRegion regionBase bs)
        (by exact pcFree_sepConj pcFree_regIs (pcFree_sepConj pcFree_regIs (bytesRegion_pcFree _ _)))
        andi_raw)
  -- BEQ x12, x0, failOff (base+8): taken ⟺ x12 = 0 ⟺ bs[1] < 0x80; convert the pure conjuncts.
  have beqS : cpsBranchWithin 1 (base + 8)
      (CodeReq.singleton (base + 8) (.BEQ .x12 .x0 failOff))
      ((.x13 ↦ᵣ (regionBase + BitVec.ofNat 64 1)) **
        (.x12 ↦ᵣ ((bs[1]'h1lt).zeroExtend 64 &&& (0x80 : Word))) ** (.x0 ↦ᵣ (0 : Word)) **
        bytesRegion regionBase bs)
      ((base + 8) + signExtend13 failOff)
        ((.x13 ↦ᵣ (regionBase + BitVec.ofNat 64 1)) **
          (.x12 ↦ᵣ ((bs[1]'h1lt).zeroExtend 64 &&& (0x80 : Word))) ** (.x0 ↦ᵣ (0 : Word)) **
          bytesRegion regionBase bs ** ⌜(bs[1]'h1lt).toNat < 0x80⌝)
      (base + 12)
        ((.x13 ↦ᵣ (regionBase + BitVec.ofNat 64 1)) **
          (.x12 ↦ᵣ ((bs[1]'h1lt).zeroExtend 64 &&& (0x80 : Word))) ** (.x0 ↦ᵣ (0 : Word)) **
          bytesRegion regionBase bs ** ⌜¬ (bs[1]'h1lt).toNat < 0x80⌝) := by
    have beq_raw := beq_spec_gen_within .x12 .x0 failOff ((bs[1]'h1lt).zeroExtend 64 &&& (0x80 : Word))
      (0 : Word) (base + 8)
    rw [show (base + 8 : Word) + 4 = base + 12 from by bv_omega] at beq_raw
    refine cpsBranchWithin_weaken (fun _ hp => by xperm_hyp hp) ?tk ?fl
      (cpsBranchWithin_frameR
        ((.x13 ↦ᵣ (regionBase + BitVec.ofNat 64 1)) ** bytesRegion regionBase bs)
        (by exact pcFree_sepConj pcFree_regIs (bytesRegion_pcFree _ _)) beq_raw)
    case tk =>
      intro h hp
      have hp' : (((.x13 ↦ᵣ (regionBase + BitVec.ofNat 64 1)) **
          (.x12 ↦ᵣ ((bs[1]'h1lt).zeroExtend 64 &&& (0x80 : Word))) ** (.x0 ↦ᵣ (0 : Word)) **
          bytesRegion regionBase bs) **
          ⌜((bs[1]'h1lt).zeroExtend 64 &&& (0x80 : Word)) = (0 : Word)⌝) h := by xperm_hyp hp
      obtain ⟨hregs, heq0⟩ := (sepConj_pure_right h).1 hp'
      have hlt : (bs[1]'h1lt).toNat < 0x80 := byte_and_0x80_zero_imp_lt _ heq0
      have hgoal := (sepConj_pure_right h).2 ⟨hregs, hlt⟩
      xperm_hyp hgoal
    case fl =>
      intro h hp
      have hp' : (((.x13 ↦ᵣ (regionBase + BitVec.ofNat 64 1)) **
          (.x12 ↦ᵣ ((bs[1]'h1lt).zeroExtend 64 &&& (0x80 : Word))) ** (.x0 ↦ᵣ (0 : Word)) **
          bytesRegion regionBase bs) **
          ⌜((bs[1]'h1lt).zeroExtend 64 &&& (0x80 : Word)) ≠ (0 : Word)⌝) h := by xperm_hyp hp
      obtain ⟨hregs, hne0⟩ := (sepConj_pure_right h).1 hp'
      have hge : ¬ (bs[1]'h1lt).toNat < 0x80 :=
        fun hlt => hne0 (byte_lt_0x80_imp_zext_and_0x80_eq_zero _ hlt)
      have hgoal := (sepConj_pure_right h).2 ⟨hregs, hge⟩
      xperm_hyp hgoal
  exact cpsTripleWithin_seq_cpsBranchWithin hd2 (cpsTripleWithin_seq hd1 lbuS andiS) beqS

-- Concrete cross-check: the validating decoder applies to a 3-byte short string `0x83 'a''b''c'`
-- (`classifyPrefix 0x83 = .shortBytes`, payload length `3 ≠ 1`), discharged by `decide`; the
-- address/disjointness side-conditions ride as parameters (a concrete program discharges them).
example (regionBase base e2_target : Word) (off1 off2 succOff : BitVec 13)
    (hover : regionBase.toNat + ((0x83 : Byte) :: [0x61, 0x62, 0x63]).length < 2 ^ 64)
    (htarget : (base + 8 + 4) + signExtend13 off2 = e2_target)
    (hd_phase3 : ((rlp_phase1_step_code 0x80 off1 base).union
                    (rlp_phase1_step_code 0xB8 off2 (base + 8))).Disjoint
                 (CodeReq.ofProg e2_target rlp_phase3_short_string_prog))
    (hd_bltu : (((rlp_phase1_step_code 0x80 off1 base).union
                    (rlp_phase1_step_code 0xB8 off2 (base + 8))).union
                 (CodeReq.ofProg e2_target rlp_phase3_short_string_prog)).Disjoint
               (CodeReq.singleton (e2_target + 8) (.BLTU .x11 .x15 succOff))) :=
  rlp_decode_shortBytes_validated (0x83 : Byte) [0x61, 0x62, 0x63] 0 0 0 0 regionBase
    off1 off2 succOff base e2_target (by decide) (by decide) hover htarget hd_phase3 hd_bltu

-- ============================================================================
-- B.1b — full shortBytes validating decoder (covers the singleton canonical case).
-- ============================================================================

set_option maxRecDepth 8000 in
/-- `decode` success for a shortBytes header whose payload fits and is canonical. -/
private theorem sbf_decode_some (pfx : Byte) (rest : List Byte)
    (h_class : classifyPrefix pfx = .shortBytes)
    (hfit : rlpPrefixShortBytesPayloadLen pfx < (pfx :: rest).length)
    (hcanon : (match rest.take (rlpPrefixShortBytesPayloadLen pfx) with
                | [b] => ¬ b.toNat < 0x80 | _ => True)) :
    decode (pfx :: rest)
      = some (.bytes (rest.take (rlpPrefixShortBytesPayloadLen pfx)),
              rest.drop (rlpPrefixShortBytesPayloadLen pfx)) := by
  set len := rlpPrefixShortBytesPayloadLen pfx
  have hle : len ≤ rest.length := by simp only [List.length_cons] at hfit; omega
  have htake : takeBytes rest len = some (rest.take len, rest.drop len) := by
    unfold takeBytes; rw [if_pos (by omega)]
  rw [decode_cons_eq_decodeAux_fuel, show 2 * rest.length + 2 = (2 * rest.length + 1) + 1 from rfl,
      decodeAux_cons_shortBytes_eq_some_iff (2 * rest.length + 1) pfx rest h_class
        (rest.take len) (rest.drop len)]
  exact ⟨rest.take len, htake, rfl, hcanon⟩

set_option maxRecDepth 8000 in
/-- `decode` rejects a shortBytes header whose declared payload does not fit. -/
private theorem sbf_decode_none_bound (pfx : Byte) (rest : List Byte)
    (h_class : classifyPrefix pfx = .shortBytes)
    (hnofit : ¬ rlpPrefixShortBytesPayloadLen pfx < (pfx :: rest).length) :
    decode (pfx :: rest) = none := by
  set len := rlpPrefixShortBytesPayloadLen pfx
  have hgt : rest.length < len := by simp only [List.length_cons] at hnofit; omega
  have htake : takeBytes rest len = none := by unfold takeBytes; rw [if_neg (by omega)]
  rw [decode_cons_eq_decodeAux_fuel, show 2 * rest.length + 2 = (2 * rest.length + 1) + 1 from rfl]
  exact decodeAux_cons_shortBytes_eq_none_of_takeBytes_none (2 * rest.length + 1) pfx rest h_class htake

set_option maxRecDepth 8000 in
/-- `decode` rejects a non-canonical singleton shortBytes (`payloadLen = 1`, payload byte `< 0x80`). -/
private theorem sbf_decode_none_singleton (pfx : Byte) (rest : List Byte)
    (h_class : classifyPrefix pfx = .shortBytes)
    (h1 : rlpPrefixShortBytesPayloadLen pfx = 1)
    (hfit : (1 : Nat) < (pfx :: rest).length)
    (hshort : (rest[0]'(by simp only [List.length_cons] at hfit; omega)).toNat < 0x80) :
    decode (pfx :: rest) = none := by
  have hrest : 0 < rest.length := by simp only [List.length_cons] at hfit; omega
  have htake : takeBytes rest (rlpPrefixShortBytesPayloadLen pfx)
      = some ([rest[0]'(by omega)], rest.drop 1) := by
    rw [h1]; unfold takeBytes; rw [if_pos (by omega)]
    cases rest with
    | nil => simp at hrest
    | cons a t => simp
  rw [decode_cons_eq_decodeAux_fuel, show 2 * rest.length + 2 = (2 * rest.length + 1) + 1 from rfl]
  exact decodeAux_cons_shortBytes_eq_none_of_singleton_short (2 * rest.length + 1) pfx
    (rest[0]'(by omega)) rest (rest.drop 1) h_class htake hshort

-- x12 = ofNat len + signExtend12 (-1) is zero iff len = 1 (len ≤ 55 < 2^64).
set_option maxRecDepth 8000 in
private theorem addi_dec_zero_iff (len : Nat) (hlen : len ≤ 55) :
    (BitVec.ofNat 64 len + signExtend12 (-(1 : BitVec 12)) = (0 : Word)) ↔ len = 1 := by
  rw [se12_neg1]
  constructor
  · intro h
    have h1 : BitVec.ofNat 64 len = (1 : Word) := by bv_omega
    have h2 := congrArg BitVec.toNat h1
    rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)] at h2
    simpa using h2
  · intro h; subst h; bv_omega

end EvmAsm.Rv64.RLP
