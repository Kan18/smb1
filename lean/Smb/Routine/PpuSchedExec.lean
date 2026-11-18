-- Generated from Smb/RefineExec.lean. Do not edit.
import Smb.Routine.PpuSched

/-! Every opcode's execution keeps the PPU's event schedule. -/
namespace Smb.Pres

set_option maxHeartbeats 1000000
set_option maxRecDepth 20000

theorem exec_00 : Pres (CPU.exec (σ := NES) 0x00) := by pres_tac
theorem exec_01 : Pres (CPU.exec (σ := NES) 0x01) := by pres_tac
theorem exec_02 : Pres (CPU.exec (σ := NES) 0x02) := by pres_tac
theorem exec_03 : Pres (CPU.exec (σ := NES) 0x03) := by pres_tac
theorem exec_04 : Pres (CPU.exec (σ := NES) 0x04) := by pres_tac
theorem exec_05 : Pres (CPU.exec (σ := NES) 0x05) := by pres_tac
theorem exec_06 : Pres (CPU.exec (σ := NES) 0x06) := by pres_tac
theorem exec_07 : Pres (CPU.exec (σ := NES) 0x07) := by pres_tac
theorem exec_08 : Pres (CPU.exec (σ := NES) 0x08) := by pres_tac
theorem exec_09 : Pres (CPU.exec (σ := NES) 0x09) := by pres_tac
theorem exec_0a : Pres (CPU.exec (σ := NES) 0x0A) := by pres_tac
theorem exec_0b : Pres (CPU.exec (σ := NES) 0x0B) := by pres_tac
theorem exec_0c : Pres (CPU.exec (σ := NES) 0x0C) := by pres_tac
theorem exec_0d : Pres (CPU.exec (σ := NES) 0x0D) := by pres_tac
theorem exec_0e : Pres (CPU.exec (σ := NES) 0x0E) := by pres_tac
theorem exec_0f : Pres (CPU.exec (σ := NES) 0x0F) := by pres_tac
theorem exec_10 : Pres (CPU.exec (σ := NES) 0x10) := by pres_tac
theorem exec_11 : Pres (CPU.exec (σ := NES) 0x11) := by pres_tac
theorem exec_12 : Pres (CPU.exec (σ := NES) 0x12) := by pres_tac
theorem exec_13 : Pres (CPU.exec (σ := NES) 0x13) := by pres_tac
theorem exec_14 : Pres (CPU.exec (σ := NES) 0x14) := by pres_tac
theorem exec_15 : Pres (CPU.exec (σ := NES) 0x15) := by pres_tac
theorem exec_16 : Pres (CPU.exec (σ := NES) 0x16) := by pres_tac
theorem exec_17 : Pres (CPU.exec (σ := NES) 0x17) := by pres_tac
theorem exec_18 : Pres (CPU.exec (σ := NES) 0x18) := by pres_tac
theorem exec_19 : Pres (CPU.exec (σ := NES) 0x19) := by pres_tac
theorem exec_1a : Pres (CPU.exec (σ := NES) 0x1A) := by pres_tac
theorem exec_1b : Pres (CPU.exec (σ := NES) 0x1B) := by pres_tac
theorem exec_1c : Pres (CPU.exec (σ := NES) 0x1C) := by pres_tac
theorem exec_1d : Pres (CPU.exec (σ := NES) 0x1D) := by pres_tac
theorem exec_1e : Pres (CPU.exec (σ := NES) 0x1E) := by pres_tac
theorem exec_1f : Pres (CPU.exec (σ := NES) 0x1F) := by pres_tac
theorem exec_20 : Pres (CPU.exec (σ := NES) 0x20) := by pres_tac
theorem exec_21 : Pres (CPU.exec (σ := NES) 0x21) := by pres_tac
theorem exec_22 : Pres (CPU.exec (σ := NES) 0x22) := by pres_tac
theorem exec_23 : Pres (CPU.exec (σ := NES) 0x23) := by pres_tac
theorem exec_24 : Pres (CPU.exec (σ := NES) 0x24) := by pres_tac
theorem exec_25 : Pres (CPU.exec (σ := NES) 0x25) := by pres_tac
theorem exec_26 : Pres (CPU.exec (σ := NES) 0x26) := by pres_tac
theorem exec_27 : Pres (CPU.exec (σ := NES) 0x27) := by pres_tac
theorem exec_28 : Pres (CPU.exec (σ := NES) 0x28) := by pres_tac
theorem exec_29 : Pres (CPU.exec (σ := NES) 0x29) := by pres_tac
theorem exec_2a : Pres (CPU.exec (σ := NES) 0x2A) := by pres_tac
theorem exec_2b : Pres (CPU.exec (σ := NES) 0x2B) := by pres_tac
theorem exec_2c : Pres (CPU.exec (σ := NES) 0x2C) := by pres_tac
theorem exec_2d : Pres (CPU.exec (σ := NES) 0x2D) := by pres_tac
theorem exec_2e : Pres (CPU.exec (σ := NES) 0x2E) := by pres_tac
theorem exec_2f : Pres (CPU.exec (σ := NES) 0x2F) := by pres_tac
theorem exec_30 : Pres (CPU.exec (σ := NES) 0x30) := by pres_tac
theorem exec_31 : Pres (CPU.exec (σ := NES) 0x31) := by pres_tac
theorem exec_32 : Pres (CPU.exec (σ := NES) 0x32) := by pres_tac
theorem exec_33 : Pres (CPU.exec (σ := NES) 0x33) := by pres_tac
theorem exec_34 : Pres (CPU.exec (σ := NES) 0x34) := by pres_tac
theorem exec_35 : Pres (CPU.exec (σ := NES) 0x35) := by pres_tac
theorem exec_36 : Pres (CPU.exec (σ := NES) 0x36) := by pres_tac
theorem exec_37 : Pres (CPU.exec (σ := NES) 0x37) := by pres_tac
theorem exec_38 : Pres (CPU.exec (σ := NES) 0x38) := by pres_tac
theorem exec_39 : Pres (CPU.exec (σ := NES) 0x39) := by pres_tac
theorem exec_3a : Pres (CPU.exec (σ := NES) 0x3A) := by pres_tac
theorem exec_3b : Pres (CPU.exec (σ := NES) 0x3B) := by pres_tac
theorem exec_3c : Pres (CPU.exec (σ := NES) 0x3C) := by pres_tac
theorem exec_3d : Pres (CPU.exec (σ := NES) 0x3D) := by pres_tac
theorem exec_3e : Pres (CPU.exec (σ := NES) 0x3E) := by pres_tac
theorem exec_3f : Pres (CPU.exec (σ := NES) 0x3F) := by pres_tac
theorem exec_40 : Pres (CPU.exec (σ := NES) 0x40) := by pres_tac
theorem exec_41 : Pres (CPU.exec (σ := NES) 0x41) := by pres_tac
theorem exec_42 : Pres (CPU.exec (σ := NES) 0x42) := by pres_tac
theorem exec_43 : Pres (CPU.exec (σ := NES) 0x43) := by pres_tac
theorem exec_44 : Pres (CPU.exec (σ := NES) 0x44) := by pres_tac
theorem exec_45 : Pres (CPU.exec (σ := NES) 0x45) := by pres_tac
theorem exec_46 : Pres (CPU.exec (σ := NES) 0x46) := by pres_tac
theorem exec_47 : Pres (CPU.exec (σ := NES) 0x47) := by pres_tac
theorem exec_48 : Pres (CPU.exec (σ := NES) 0x48) := by pres_tac
theorem exec_49 : Pres (CPU.exec (σ := NES) 0x49) := by pres_tac
theorem exec_4a : Pres (CPU.exec (σ := NES) 0x4A) := by pres_tac
theorem exec_4b : Pres (CPU.exec (σ := NES) 0x4B) := by pres_tac
theorem exec_4c : Pres (CPU.exec (σ := NES) 0x4C) := by pres_tac
theorem exec_4d : Pres (CPU.exec (σ := NES) 0x4D) := by pres_tac
theorem exec_4e : Pres (CPU.exec (σ := NES) 0x4E) := by pres_tac
theorem exec_4f : Pres (CPU.exec (σ := NES) 0x4F) := by pres_tac
theorem exec_50 : Pres (CPU.exec (σ := NES) 0x50) := by pres_tac
theorem exec_51 : Pres (CPU.exec (σ := NES) 0x51) := by pres_tac
theorem exec_52 : Pres (CPU.exec (σ := NES) 0x52) := by pres_tac
theorem exec_53 : Pres (CPU.exec (σ := NES) 0x53) := by pres_tac
theorem exec_54 : Pres (CPU.exec (σ := NES) 0x54) := by pres_tac
theorem exec_55 : Pres (CPU.exec (σ := NES) 0x55) := by pres_tac
theorem exec_56 : Pres (CPU.exec (σ := NES) 0x56) := by pres_tac
theorem exec_57 : Pres (CPU.exec (σ := NES) 0x57) := by pres_tac
theorem exec_58 : Pres (CPU.exec (σ := NES) 0x58) := by pres_tac
theorem exec_59 : Pres (CPU.exec (σ := NES) 0x59) := by pres_tac
theorem exec_5a : Pres (CPU.exec (σ := NES) 0x5A) := by pres_tac
theorem exec_5b : Pres (CPU.exec (σ := NES) 0x5B) := by pres_tac
theorem exec_5c : Pres (CPU.exec (σ := NES) 0x5C) := by pres_tac
theorem exec_5d : Pres (CPU.exec (σ := NES) 0x5D) := by pres_tac
theorem exec_5e : Pres (CPU.exec (σ := NES) 0x5E) := by pres_tac
theorem exec_5f : Pres (CPU.exec (σ := NES) 0x5F) := by pres_tac
theorem exec_60 : Pres (CPU.exec (σ := NES) 0x60) := by pres_tac
theorem exec_61 : Pres (CPU.exec (σ := NES) 0x61) := by pres_tac
theorem exec_62 : Pres (CPU.exec (σ := NES) 0x62) := by pres_tac
theorem exec_63 : Pres (CPU.exec (σ := NES) 0x63) := by pres_tac
theorem exec_64 : Pres (CPU.exec (σ := NES) 0x64) := by pres_tac
theorem exec_65 : Pres (CPU.exec (σ := NES) 0x65) := by pres_tac
theorem exec_66 : Pres (CPU.exec (σ := NES) 0x66) := by pres_tac
theorem exec_67 : Pres (CPU.exec (σ := NES) 0x67) := by pres_tac
theorem exec_68 : Pres (CPU.exec (σ := NES) 0x68) := by pres_tac
theorem exec_69 : Pres (CPU.exec (σ := NES) 0x69) := by pres_tac
theorem exec_6a : Pres (CPU.exec (σ := NES) 0x6A) := by pres_tac
theorem exec_6b : Pres (CPU.exec (σ := NES) 0x6B) := by pres_tac
theorem exec_6c : Pres (CPU.exec (σ := NES) 0x6C) := by pres_tac
theorem exec_6d : Pres (CPU.exec (σ := NES) 0x6D) := by pres_tac
theorem exec_6e : Pres (CPU.exec (σ := NES) 0x6E) := by pres_tac
theorem exec_6f : Pres (CPU.exec (σ := NES) 0x6F) := by pres_tac
theorem exec_70 : Pres (CPU.exec (σ := NES) 0x70) := by pres_tac
theorem exec_71 : Pres (CPU.exec (σ := NES) 0x71) := by pres_tac
theorem exec_72 : Pres (CPU.exec (σ := NES) 0x72) := by pres_tac
theorem exec_73 : Pres (CPU.exec (σ := NES) 0x73) := by pres_tac
theorem exec_74 : Pres (CPU.exec (σ := NES) 0x74) := by pres_tac
theorem exec_75 : Pres (CPU.exec (σ := NES) 0x75) := by pres_tac
theorem exec_76 : Pres (CPU.exec (σ := NES) 0x76) := by pres_tac
theorem exec_77 : Pres (CPU.exec (σ := NES) 0x77) := by pres_tac
theorem exec_78 : Pres (CPU.exec (σ := NES) 0x78) := by pres_tac
theorem exec_79 : Pres (CPU.exec (σ := NES) 0x79) := by pres_tac
theorem exec_7a : Pres (CPU.exec (σ := NES) 0x7A) := by pres_tac
theorem exec_7b : Pres (CPU.exec (σ := NES) 0x7B) := by pres_tac
theorem exec_7c : Pres (CPU.exec (σ := NES) 0x7C) := by pres_tac
theorem exec_7d : Pres (CPU.exec (σ := NES) 0x7D) := by pres_tac
theorem exec_7e : Pres (CPU.exec (σ := NES) 0x7E) := by pres_tac
theorem exec_7f : Pres (CPU.exec (σ := NES) 0x7F) := by pres_tac
theorem exec_80 : Pres (CPU.exec (σ := NES) 0x80) := by pres_tac
theorem exec_81 : Pres (CPU.exec (σ := NES) 0x81) := by pres_tac
theorem exec_82 : Pres (CPU.exec (σ := NES) 0x82) := by pres_tac
theorem exec_83 : Pres (CPU.exec (σ := NES) 0x83) := by pres_tac
theorem exec_84 : Pres (CPU.exec (σ := NES) 0x84) := by pres_tac
theorem exec_85 : Pres (CPU.exec (σ := NES) 0x85) := by pres_tac
theorem exec_86 : Pres (CPU.exec (σ := NES) 0x86) := by pres_tac
theorem exec_87 : Pres (CPU.exec (σ := NES) 0x87) := by pres_tac
theorem exec_88 : Pres (CPU.exec (σ := NES) 0x88) := by pres_tac
theorem exec_89 : Pres (CPU.exec (σ := NES) 0x89) := by pres_tac
theorem exec_8a : Pres (CPU.exec (σ := NES) 0x8A) := by pres_tac
theorem exec_8b : Pres (CPU.exec (σ := NES) 0x8B) := by pres_tac
theorem exec_8c : Pres (CPU.exec (σ := NES) 0x8C) := by pres_tac
theorem exec_8d : Pres (CPU.exec (σ := NES) 0x8D) := by pres_tac
theorem exec_8e : Pres (CPU.exec (σ := NES) 0x8E) := by pres_tac
theorem exec_8f : Pres (CPU.exec (σ := NES) 0x8F) := by pres_tac
theorem exec_90 : Pres (CPU.exec (σ := NES) 0x90) := by pres_tac
theorem exec_91 : Pres (CPU.exec (σ := NES) 0x91) := by pres_tac
theorem exec_92 : Pres (CPU.exec (σ := NES) 0x92) := by pres_tac
theorem exec_93 : Pres (CPU.exec (σ := NES) 0x93) := by pres_tac
theorem exec_94 : Pres (CPU.exec (σ := NES) 0x94) := by pres_tac
theorem exec_95 : Pres (CPU.exec (σ := NES) 0x95) := by pres_tac
theorem exec_96 : Pres (CPU.exec (σ := NES) 0x96) := by pres_tac
theorem exec_97 : Pres (CPU.exec (σ := NES) 0x97) := by pres_tac
theorem exec_98 : Pres (CPU.exec (σ := NES) 0x98) := by pres_tac
theorem exec_99 : Pres (CPU.exec (σ := NES) 0x99) := by pres_tac
theorem exec_9a : Pres (CPU.exec (σ := NES) 0x9A) := by pres_tac
theorem exec_9b : Pres (CPU.exec (σ := NES) 0x9B) := by pres_tac
theorem exec_9c : Pres (CPU.exec (σ := NES) 0x9C) := by pres_tac
theorem exec_9d : Pres (CPU.exec (σ := NES) 0x9D) := by pres_tac
theorem exec_9e : Pres (CPU.exec (σ := NES) 0x9E) := by pres_tac
theorem exec_9f : Pres (CPU.exec (σ := NES) 0x9F) := by pres_tac
theorem exec_a0 : Pres (CPU.exec (σ := NES) 0xA0) := by pres_tac
theorem exec_a1 : Pres (CPU.exec (σ := NES) 0xA1) := by pres_tac
theorem exec_a2 : Pres (CPU.exec (σ := NES) 0xA2) := by pres_tac
theorem exec_a3 : Pres (CPU.exec (σ := NES) 0xA3) := by pres_tac
theorem exec_a4 : Pres (CPU.exec (σ := NES) 0xA4) := by pres_tac
theorem exec_a5 : Pres (CPU.exec (σ := NES) 0xA5) := by pres_tac
theorem exec_a6 : Pres (CPU.exec (σ := NES) 0xA6) := by pres_tac
theorem exec_a7 : Pres (CPU.exec (σ := NES) 0xA7) := by pres_tac
theorem exec_a8 : Pres (CPU.exec (σ := NES) 0xA8) := by pres_tac
theorem exec_a9 : Pres (CPU.exec (σ := NES) 0xA9) := by pres_tac
theorem exec_aa : Pres (CPU.exec (σ := NES) 0xAA) := by pres_tac
theorem exec_ab : Pres (CPU.exec (σ := NES) 0xAB) := by pres_tac
theorem exec_ac : Pres (CPU.exec (σ := NES) 0xAC) := by pres_tac
theorem exec_ad : Pres (CPU.exec (σ := NES) 0xAD) := by pres_tac
theorem exec_ae : Pres (CPU.exec (σ := NES) 0xAE) := by pres_tac
theorem exec_af : Pres (CPU.exec (σ := NES) 0xAF) := by pres_tac
theorem exec_b0 : Pres (CPU.exec (σ := NES) 0xB0) := by pres_tac
theorem exec_b1 : Pres (CPU.exec (σ := NES) 0xB1) := by pres_tac
theorem exec_b2 : Pres (CPU.exec (σ := NES) 0xB2) := by pres_tac
theorem exec_b3 : Pres (CPU.exec (σ := NES) 0xB3) := by pres_tac
theorem exec_b4 : Pres (CPU.exec (σ := NES) 0xB4) := by pres_tac
theorem exec_b5 : Pres (CPU.exec (σ := NES) 0xB5) := by pres_tac
theorem exec_b6 : Pres (CPU.exec (σ := NES) 0xB6) := by pres_tac
theorem exec_b7 : Pres (CPU.exec (σ := NES) 0xB7) := by pres_tac
theorem exec_b8 : Pres (CPU.exec (σ := NES) 0xB8) := by pres_tac
theorem exec_b9 : Pres (CPU.exec (σ := NES) 0xB9) := by pres_tac
theorem exec_ba : Pres (CPU.exec (σ := NES) 0xBA) := by pres_tac
theorem exec_bb : Pres (CPU.exec (σ := NES) 0xBB) := by pres_tac
theorem exec_bc : Pres (CPU.exec (σ := NES) 0xBC) := by pres_tac
theorem exec_bd : Pres (CPU.exec (σ := NES) 0xBD) := by pres_tac
theorem exec_be : Pres (CPU.exec (σ := NES) 0xBE) := by pres_tac
theorem exec_bf : Pres (CPU.exec (σ := NES) 0xBF) := by pres_tac
theorem exec_c0 : Pres (CPU.exec (σ := NES) 0xC0) := by pres_tac
theorem exec_c1 : Pres (CPU.exec (σ := NES) 0xC1) := by pres_tac
theorem exec_c2 : Pres (CPU.exec (σ := NES) 0xC2) := by pres_tac
theorem exec_c3 : Pres (CPU.exec (σ := NES) 0xC3) := by pres_tac
theorem exec_c4 : Pres (CPU.exec (σ := NES) 0xC4) := by pres_tac
theorem exec_c5 : Pres (CPU.exec (σ := NES) 0xC5) := by pres_tac
theorem exec_c6 : Pres (CPU.exec (σ := NES) 0xC6) := by pres_tac
theorem exec_c7 : Pres (CPU.exec (σ := NES) 0xC7) := by pres_tac
theorem exec_c8 : Pres (CPU.exec (σ := NES) 0xC8) := by pres_tac
theorem exec_c9 : Pres (CPU.exec (σ := NES) 0xC9) := by pres_tac
theorem exec_ca : Pres (CPU.exec (σ := NES) 0xCA) := by pres_tac
theorem exec_cb : Pres (CPU.exec (σ := NES) 0xCB) := by pres_tac
theorem exec_cc : Pres (CPU.exec (σ := NES) 0xCC) := by pres_tac
theorem exec_cd : Pres (CPU.exec (σ := NES) 0xCD) := by pres_tac
theorem exec_ce : Pres (CPU.exec (σ := NES) 0xCE) := by pres_tac
theorem exec_cf : Pres (CPU.exec (σ := NES) 0xCF) := by pres_tac
theorem exec_d0 : Pres (CPU.exec (σ := NES) 0xD0) := by pres_tac
theorem exec_d1 : Pres (CPU.exec (σ := NES) 0xD1) := by pres_tac
theorem exec_d2 : Pres (CPU.exec (σ := NES) 0xD2) := by pres_tac
theorem exec_d3 : Pres (CPU.exec (σ := NES) 0xD3) := by pres_tac
theorem exec_d4 : Pres (CPU.exec (σ := NES) 0xD4) := by pres_tac
theorem exec_d5 : Pres (CPU.exec (σ := NES) 0xD5) := by pres_tac
theorem exec_d6 : Pres (CPU.exec (σ := NES) 0xD6) := by pres_tac
theorem exec_d7 : Pres (CPU.exec (σ := NES) 0xD7) := by pres_tac
theorem exec_d8 : Pres (CPU.exec (σ := NES) 0xD8) := by pres_tac
theorem exec_d9 : Pres (CPU.exec (σ := NES) 0xD9) := by pres_tac
theorem exec_da : Pres (CPU.exec (σ := NES) 0xDA) := by pres_tac
theorem exec_db : Pres (CPU.exec (σ := NES) 0xDB) := by pres_tac
theorem exec_dc : Pres (CPU.exec (σ := NES) 0xDC) := by pres_tac
theorem exec_dd : Pres (CPU.exec (σ := NES) 0xDD) := by pres_tac
theorem exec_de : Pres (CPU.exec (σ := NES) 0xDE) := by pres_tac
theorem exec_df : Pres (CPU.exec (σ := NES) 0xDF) := by pres_tac
theorem exec_e0 : Pres (CPU.exec (σ := NES) 0xE0) := by pres_tac
theorem exec_e1 : Pres (CPU.exec (σ := NES) 0xE1) := by pres_tac
theorem exec_e2 : Pres (CPU.exec (σ := NES) 0xE2) := by pres_tac
theorem exec_e3 : Pres (CPU.exec (σ := NES) 0xE3) := by pres_tac
theorem exec_e4 : Pres (CPU.exec (σ := NES) 0xE4) := by pres_tac
theorem exec_e5 : Pres (CPU.exec (σ := NES) 0xE5) := by pres_tac
theorem exec_e6 : Pres (CPU.exec (σ := NES) 0xE6) := by pres_tac
theorem exec_e7 : Pres (CPU.exec (σ := NES) 0xE7) := by pres_tac
theorem exec_e8 : Pres (CPU.exec (σ := NES) 0xE8) := by pres_tac
theorem exec_e9 : Pres (CPU.exec (σ := NES) 0xE9) := by pres_tac
theorem exec_ea : Pres (CPU.exec (σ := NES) 0xEA) := by pres_tac
theorem exec_eb : Pres (CPU.exec (σ := NES) 0xEB) := by pres_tac
theorem exec_ec : Pres (CPU.exec (σ := NES) 0xEC) := by pres_tac
theorem exec_ed : Pres (CPU.exec (σ := NES) 0xED) := by pres_tac
theorem exec_ee : Pres (CPU.exec (σ := NES) 0xEE) := by pres_tac
theorem exec_ef : Pres (CPU.exec (σ := NES) 0xEF) := by pres_tac
theorem exec_f0 : Pres (CPU.exec (σ := NES) 0xF0) := by pres_tac
theorem exec_f1 : Pres (CPU.exec (σ := NES) 0xF1) := by pres_tac
theorem exec_f2 : Pres (CPU.exec (σ := NES) 0xF2) := by pres_tac
theorem exec_f3 : Pres (CPU.exec (σ := NES) 0xF3) := by pres_tac
theorem exec_f4 : Pres (CPU.exec (σ := NES) 0xF4) := by pres_tac
theorem exec_f5 : Pres (CPU.exec (σ := NES) 0xF5) := by pres_tac
theorem exec_f6 : Pres (CPU.exec (σ := NES) 0xF6) := by pres_tac
theorem exec_f7 : Pres (CPU.exec (σ := NES) 0xF7) := by pres_tac
theorem exec_f8 : Pres (CPU.exec (σ := NES) 0xF8) := by pres_tac
theorem exec_f9 : Pres (CPU.exec (σ := NES) 0xF9) := by pres_tac
theorem exec_fa : Pres (CPU.exec (σ := NES) 0xFA) := by pres_tac
theorem exec_fb : Pres (CPU.exec (σ := NES) 0xFB) := by pres_tac
theorem exec_fc : Pres (CPU.exec (σ := NES) 0xFC) := by pres_tac
theorem exec_fd : Pres (CPU.exec (σ := NES) 0xFD) := by pres_tac
theorem exec_fe : Pres (CPU.exec (σ := NES) 0xFE) := by pres_tac
theorem exec_ff : Pres (CPU.exec (σ := NES) 0xFF) := by pres_tac

/-- Case analysis on the opcode's underlying number. (An `rcases` over a 256-way
disjunction is ~300× slower to check.) -/
theorem exec (op : UInt8) : Pres (CPU.exec (σ := NES) op) := by
  obtain ⟨⟨⟨n, hn⟩⟩⟩ := op
  match n, hn with
  | 0, _ => exact exec_00
  | 1, _ => exact exec_01
  | 2, _ => exact exec_02
  | 3, _ => exact exec_03
  | 4, _ => exact exec_04
  | 5, _ => exact exec_05
  | 6, _ => exact exec_06
  | 7, _ => exact exec_07
  | 8, _ => exact exec_08
  | 9, _ => exact exec_09
  | 10, _ => exact exec_0a
  | 11, _ => exact exec_0b
  | 12, _ => exact exec_0c
  | 13, _ => exact exec_0d
  | 14, _ => exact exec_0e
  | 15, _ => exact exec_0f
  | 16, _ => exact exec_10
  | 17, _ => exact exec_11
  | 18, _ => exact exec_12
  | 19, _ => exact exec_13
  | 20, _ => exact exec_14
  | 21, _ => exact exec_15
  | 22, _ => exact exec_16
  | 23, _ => exact exec_17
  | 24, _ => exact exec_18
  | 25, _ => exact exec_19
  | 26, _ => exact exec_1a
  | 27, _ => exact exec_1b
  | 28, _ => exact exec_1c
  | 29, _ => exact exec_1d
  | 30, _ => exact exec_1e
  | 31, _ => exact exec_1f
  | 32, _ => exact exec_20
  | 33, _ => exact exec_21
  | 34, _ => exact exec_22
  | 35, _ => exact exec_23
  | 36, _ => exact exec_24
  | 37, _ => exact exec_25
  | 38, _ => exact exec_26
  | 39, _ => exact exec_27
  | 40, _ => exact exec_28
  | 41, _ => exact exec_29
  | 42, _ => exact exec_2a
  | 43, _ => exact exec_2b
  | 44, _ => exact exec_2c
  | 45, _ => exact exec_2d
  | 46, _ => exact exec_2e
  | 47, _ => exact exec_2f
  | 48, _ => exact exec_30
  | 49, _ => exact exec_31
  | 50, _ => exact exec_32
  | 51, _ => exact exec_33
  | 52, _ => exact exec_34
  | 53, _ => exact exec_35
  | 54, _ => exact exec_36
  | 55, _ => exact exec_37
  | 56, _ => exact exec_38
  | 57, _ => exact exec_39
  | 58, _ => exact exec_3a
  | 59, _ => exact exec_3b
  | 60, _ => exact exec_3c
  | 61, _ => exact exec_3d
  | 62, _ => exact exec_3e
  | 63, _ => exact exec_3f
  | 64, _ => exact exec_40
  | 65, _ => exact exec_41
  | 66, _ => exact exec_42
  | 67, _ => exact exec_43
  | 68, _ => exact exec_44
  | 69, _ => exact exec_45
  | 70, _ => exact exec_46
  | 71, _ => exact exec_47
  | 72, _ => exact exec_48
  | 73, _ => exact exec_49
  | 74, _ => exact exec_4a
  | 75, _ => exact exec_4b
  | 76, _ => exact exec_4c
  | 77, _ => exact exec_4d
  | 78, _ => exact exec_4e
  | 79, _ => exact exec_4f
  | 80, _ => exact exec_50
  | 81, _ => exact exec_51
  | 82, _ => exact exec_52
  | 83, _ => exact exec_53
  | 84, _ => exact exec_54
  | 85, _ => exact exec_55
  | 86, _ => exact exec_56
  | 87, _ => exact exec_57
  | 88, _ => exact exec_58
  | 89, _ => exact exec_59
  | 90, _ => exact exec_5a
  | 91, _ => exact exec_5b
  | 92, _ => exact exec_5c
  | 93, _ => exact exec_5d
  | 94, _ => exact exec_5e
  | 95, _ => exact exec_5f
  | 96, _ => exact exec_60
  | 97, _ => exact exec_61
  | 98, _ => exact exec_62
  | 99, _ => exact exec_63
  | 100, _ => exact exec_64
  | 101, _ => exact exec_65
  | 102, _ => exact exec_66
  | 103, _ => exact exec_67
  | 104, _ => exact exec_68
  | 105, _ => exact exec_69
  | 106, _ => exact exec_6a
  | 107, _ => exact exec_6b
  | 108, _ => exact exec_6c
  | 109, _ => exact exec_6d
  | 110, _ => exact exec_6e
  | 111, _ => exact exec_6f
  | 112, _ => exact exec_70
  | 113, _ => exact exec_71
  | 114, _ => exact exec_72
  | 115, _ => exact exec_73
  | 116, _ => exact exec_74
  | 117, _ => exact exec_75
  | 118, _ => exact exec_76
  | 119, _ => exact exec_77
  | 120, _ => exact exec_78
  | 121, _ => exact exec_79
  | 122, _ => exact exec_7a
  | 123, _ => exact exec_7b
  | 124, _ => exact exec_7c
  | 125, _ => exact exec_7d
  | 126, _ => exact exec_7e
  | 127, _ => exact exec_7f
  | 128, _ => exact exec_80
  | 129, _ => exact exec_81
  | 130, _ => exact exec_82
  | 131, _ => exact exec_83
  | 132, _ => exact exec_84
  | 133, _ => exact exec_85
  | 134, _ => exact exec_86
  | 135, _ => exact exec_87
  | 136, _ => exact exec_88
  | 137, _ => exact exec_89
  | 138, _ => exact exec_8a
  | 139, _ => exact exec_8b
  | 140, _ => exact exec_8c
  | 141, _ => exact exec_8d
  | 142, _ => exact exec_8e
  | 143, _ => exact exec_8f
  | 144, _ => exact exec_90
  | 145, _ => exact exec_91
  | 146, _ => exact exec_92
  | 147, _ => exact exec_93
  | 148, _ => exact exec_94
  | 149, _ => exact exec_95
  | 150, _ => exact exec_96
  | 151, _ => exact exec_97
  | 152, _ => exact exec_98
  | 153, _ => exact exec_99
  | 154, _ => exact exec_9a
  | 155, _ => exact exec_9b
  | 156, _ => exact exec_9c
  | 157, _ => exact exec_9d
  | 158, _ => exact exec_9e
  | 159, _ => exact exec_9f
  | 160, _ => exact exec_a0
  | 161, _ => exact exec_a1
  | 162, _ => exact exec_a2
  | 163, _ => exact exec_a3
  | 164, _ => exact exec_a4
  | 165, _ => exact exec_a5
  | 166, _ => exact exec_a6
  | 167, _ => exact exec_a7
  | 168, _ => exact exec_a8
  | 169, _ => exact exec_a9
  | 170, _ => exact exec_aa
  | 171, _ => exact exec_ab
  | 172, _ => exact exec_ac
  | 173, _ => exact exec_ad
  | 174, _ => exact exec_ae
  | 175, _ => exact exec_af
  | 176, _ => exact exec_b0
  | 177, _ => exact exec_b1
  | 178, _ => exact exec_b2
  | 179, _ => exact exec_b3
  | 180, _ => exact exec_b4
  | 181, _ => exact exec_b5
  | 182, _ => exact exec_b6
  | 183, _ => exact exec_b7
  | 184, _ => exact exec_b8
  | 185, _ => exact exec_b9
  | 186, _ => exact exec_ba
  | 187, _ => exact exec_bb
  | 188, _ => exact exec_bc
  | 189, _ => exact exec_bd
  | 190, _ => exact exec_be
  | 191, _ => exact exec_bf
  | 192, _ => exact exec_c0
  | 193, _ => exact exec_c1
  | 194, _ => exact exec_c2
  | 195, _ => exact exec_c3
  | 196, _ => exact exec_c4
  | 197, _ => exact exec_c5
  | 198, _ => exact exec_c6
  | 199, _ => exact exec_c7
  | 200, _ => exact exec_c8
  | 201, _ => exact exec_c9
  | 202, _ => exact exec_ca
  | 203, _ => exact exec_cb
  | 204, _ => exact exec_cc
  | 205, _ => exact exec_cd
  | 206, _ => exact exec_ce
  | 207, _ => exact exec_cf
  | 208, _ => exact exec_d0
  | 209, _ => exact exec_d1
  | 210, _ => exact exec_d2
  | 211, _ => exact exec_d3
  | 212, _ => exact exec_d4
  | 213, _ => exact exec_d5
  | 214, _ => exact exec_d6
  | 215, _ => exact exec_d7
  | 216, _ => exact exec_d8
  | 217, _ => exact exec_d9
  | 218, _ => exact exec_da
  | 219, _ => exact exec_db
  | 220, _ => exact exec_dc
  | 221, _ => exact exec_dd
  | 222, _ => exact exec_de
  | 223, _ => exact exec_df
  | 224, _ => exact exec_e0
  | 225, _ => exact exec_e1
  | 226, _ => exact exec_e2
  | 227, _ => exact exec_e3
  | 228, _ => exact exec_e4
  | 229, _ => exact exec_e5
  | 230, _ => exact exec_e6
  | 231, _ => exact exec_e7
  | 232, _ => exact exec_e8
  | 233, _ => exact exec_e9
  | 234, _ => exact exec_ea
  | 235, _ => exact exec_eb
  | 236, _ => exact exec_ec
  | 237, _ => exact exec_ed
  | 238, _ => exact exec_ee
  | 239, _ => exact exec_ef
  | 240, _ => exact exec_f0
  | 241, _ => exact exec_f1
  | 242, _ => exact exec_f2
  | 243, _ => exact exec_f3
  | 244, _ => exact exec_f4
  | 245, _ => exact exec_f5
  | 246, _ => exact exec_f6
  | 247, _ => exact exec_f7
  | 248, _ => exact exec_f8
  | 249, _ => exact exec_f9
  | 250, _ => exact exec_fa
  | 251, _ => exact exec_fb
  | 252, _ => exact exec_fc
  | 253, _ => exact exec_fd
  | 254, _ => exact exec_fe
  | 255, _ => exact exec_ff
  | n + 256, h => exact absurd h (by omega)

theorem fetch : Pres (CPU.fetch (σ := NES)) := by pres_tac

theorem stepTail (op : UInt8) : Pres (CPU.stepTail (σ := NES) op) := by
  unfold CPU.stepTail
  refine Pres.bind (exec op) (fun _ => ?_)
  pres_tac

theorem step : Pres (CPU.step (σ := NES)) := by
  unfold CPU.step
  exact Pres.bind fetch stepTail

end Smb.Pres
