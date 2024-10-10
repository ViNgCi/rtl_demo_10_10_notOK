`ifdef RISCV_FORMAL
  `define RVFI
`endif

// `include "prim_assert.sv"
// `include "dv_fcov_macros.svh"

/**
 * Top level module of the ibex RISC-V core
 */

module riscv_core import ibex_pkg::*; #(
  parameter bit                     PMPEnable        = 1'b0,
  parameter int unsigned            PMPGranularity   = 0,
  parameter int unsigned            PMPNumRegions    = 4,
  parameter ibex_pkg::pmp_cfg_t     PMPRstCfg[16]    = ibex_pkg::PmpCfgRst,
  parameter logic [33:0]            PMPRstAddr[16]   = ibex_pkg::PmpAddrRst,
  parameter ibex_pkg::pmp_mseccfg_t PMPRstMsecCfg    = ibex_pkg::PmpMseccfgRst,
  parameter int unsigned            MHPMCounterNum   = 0,
  parameter int unsigned            MHPMCounterWidth = 40,
  parameter bit                     RV32E            = 1'b0,
  parameter rv32m_e                 RV32M            = RV32MFast,
  parameter rv32b_e                 RV32B            = RV32BNone,
  parameter bit                     BranchTargetALU  = 1'b0,
  parameter bit                     WritebackStage   = 1'b0,
  parameter bit                     ICache           = 1'b0,
  parameter bit                     ICacheECC        = 1'b0,
  parameter int unsigned            BusSizeECC       = BUS_SIZE,
  parameter int unsigned            TagSizeECC       = IC_TAG_SIZE,
  parameter int unsigned            LineSizeECC      = IC_LINE_SIZE,
  parameter bit                     BranchPredictor  = 1'b0,
  parameter bit                     DbgTriggerEn     = 1'b0,
  parameter int unsigned            DbgHwBreakNum    = 1,
  parameter bit                     ResetAll         = 1'b0,
  parameter lfsr_seed_t             RndCnstLfsrSeed  = RndCnstLfsrSeedDefault,
  parameter lfsr_perm_t             RndCnstLfsrPerm  = RndCnstLfsrPermDefault,
  parameter bit                     SecureIbex       = 1'b0,
  parameter bit                     DummyInstructions= 1'b0,
  parameter bit                     RegFileECC       = 1'b0,
  parameter int unsigned            RegFileDataWidth = 32,
  parameter bit                     MemECC           = 1'b0,
  parameter int unsigned            MemDataWidth     = MemECC ? 32 + 7 : 32,
  parameter int unsigned            DmHaltAddr       = 32'h1A110800,
  parameter int unsigned            DmExceptionAddr  = 32'h1A110808
)(
  // Clock and Reset
  input  logic                         clk_i,
  input  logic                         rst_ni,
  input  logic [31:0]                  hart_id_i,
  input  logic [31:0]                  boot_addr_i,

  // Instruction memory interface
  output logic                         instr_req_o,
  input  logic                         instr_gnt_i,
  input  logic                         instr_rvalid_i,
  output logic [31:0]                  instr_addr_o,
  input  logic [MemDataWidth-1:0]      instr_rdata_i,
  input  logic                         instr_err_i,

  // Data memory interface
  output logic                         data_req_o,
  input  logic                         data_gnt_i,
  input  logic                         data_rvalid_i,
  output logic                         data_we_o,
  output logic [3:0]                   data_be_o,
  output logic [31:0]                  data_addr_o,
  output logic [MemDataWidth-1:0]      data_wdata_o,
  input  logic [MemDataWidth-1:0]      data_rdata_i,
  input  logic                         data_err_i,

  // Register file interface
  output logic                         dummy_instr_id_o,
  output logic                         dummy_instr_wb_o,
  output logic [4:0]                   rf_raddr_a_o,
  output logic [4:0]                   rf_raddr_b_o,
  output logic [4:0]                   rf_waddr_wb_o,
  output logic                         rf_we_wb_o,
  output logic [RegFileDataWidth-1:0]  rf_wdata_wb_ecc_o,
  input  logic [RegFileDataWidth-1:0]  rf_rdata_a_ecc_i,
  input  logic [RegFileDataWidth-1:0]  rf_rdata_b_ecc_i,

  // RAMs interface
  output logic [IC_NUM_WAYS-1:0]       ic_tag_req_o,
  output logic                         ic_tag_write_o,
  output logic [IC_INDEX_W-1:0]        ic_tag_addr_o,
  output logic [TagSizeECC-1:0]        ic_tag_wdata_o,
  input  logic [TagSizeECC-1:0]        ic_tag_rdata_i [IC_NUM_WAYS],
  output logic [IC_NUM_WAYS-1:0]       ic_data_req_o,
  output logic                         ic_data_write_o,
  output logic [IC_INDEX_W-1:0]        ic_data_addr_o,
  output logic [LineSizeECC-1:0]       ic_data_wdata_o,
  input  logic [LineSizeECC-1:0]       ic_data_rdata_i [IC_NUM_WAYS],
  input  logic                         ic_scr_key_valid_i,
  output logic                         ic_scr_key_req_o,

  // Interrupt inputs
  input  logic                         irq_software_i,
  input  logic                         irq_timer_i,
  input  logic                         irq_external_i,
  input  logic [14:0]                  irq_fast_i,
  input  logic                         irq_nm_i,       // non-maskeable interrupt
  output logic                         irq_pending_o,

  // Debug Interface
  input  logic                         debug_req_i,
  output crash_dump_t                  crash_dump_o,
  // SEC_CM: EXCEPTION.CTRL_FLOW.LOCAL_ESC
  // SEC_CM: EXCEPTION.CTRL_FLOW.GLOBAL_ESC
  output logic                         double_fault_seen_o,

  // RISC-V Formal Interface
  // Does not comply with the coding standards of _i/_o suffixes, but follows
  // the convention of RISC-V Formal Interface Specification.
`ifdef RVFI
  output logic                         rvfi_valid,
  output logic [63:0]                  rvfi_order,
  output logic [31:0]                  rvfi_insn,
  output logic                         rvfi_trap,
  output logic                         rvfi_halt,
  output logic                         rvfi_intr,
  output logic [ 1:0]                  rvfi_mode,
  output logic [ 1:0]                  rvfi_ixl,
  output logic [ 4:0]                  rvfi_rs1_addr,
  output logic [ 4:0]                  rvfi_rs2_addr,
  output logic [ 4:0]                  rvfi_rs3_addr,
  output logic [31:0]                  rvfi_rs1_rdata,
  output logic [31:0]                  rvfi_rs2_rdata,
  output logic [31:0]                  rvfi_rs3_rdata,
  output logic [ 4:0]                  rvfi_rd_addr,
  output logic [31:0]                  rvfi_rd_wdata,
  output logic [31:0]                  rvfi_pc_rdata,
  output logic [31:0]                  rvfi_pc_wdata,
  output logic [31:0]                  rvfi_mem_addr,
  output logic [ 3:0]                  rvfi_mem_rmask,
  output logic [ 3:0]                  rvfi_mem_wmask,
  output logic [31:0]                  rvfi_mem_rdata,
  output logic [31:0]                  rvfi_mem_wdata,
  output logic [31:0]                  rvfi_ext_pre_mip,
  output logic [31:0]                  rvfi_ext_post_mip,
  output logic                         rvfi_ext_nmi,
  output logic                         rvfi_ext_nmi_int,
  output logic                         rvfi_ext_debug_req,
  output logic                         rvfi_ext_debug_mode,
  output logic                         rvfi_ext_rf_wr_suppress,
  output logic [63:0]                  rvfi_ext_mcycle,
  output logic [31:0]                  rvfi_ext_mhpmcounters [10],
  output logic [31:0]                  rvfi_ext_mhpmcountersh [10],
  output logic                         rvfi_ext_ic_scr_key_valid,
  output logic                         rvfi_ext_irq_valid,
  `endif

  // CPU Control Signals
  // SEC_CM: FETCH.CTRL.LC_GATED
  input  ibex_mubi_t                   fetch_enable_i,
  output logic                         alert_minor_o,
  output logic                         alert_major_internal_o,
  output logic                         alert_major_bus_o,
  output ibex_mubi_t                   core_busy_o
);

  //////////////////////
  // Clock management //
  //////////////////////

  localparam int unsigned PMPNumChan      = 3;
  // SEC_CM: CORE.DATA_REG_SW.SCA
  localparam bit          DataIndTiming     = SecureIbex;
  localparam bit          PCIncrCheck       = SecureIbex;
  localparam bit          ShadowCSR         = 1'b0;

  //////////////////////
  //   Signals List   //
  //////////////////////

  // IF/ID signals
  logic        dummy_instr_id;
  logic        instr_valid_id;
  logic        instr_new_id;
  logic [31:0] instr_rdata_id;                 // Instruction sampled inside IF stage
  logic [31:0] instr_rdata_alu_id;             // Instruction sampled inside IF stage (replicated to
                                               // ease fan-out)
  logic [15:0] instr_rdata_c_id;               // Compressed instruction sampled inside IF stage
  logic        instr_is_compressed_id;
  logic        instr_perf_count_id;
  logic        instr_bp_taken_id;
  logic        instr_fetch_err;                // Bus error on instr fetch
  logic        instr_fetch_err_plus2;          // Instruction error is misaligned
  logic        illegal_c_insn_id;              // Illegal compressed instruction sent to ID stage
  logic [31:0] pc_if;                          // Program counter in IF stage
  logic [31:0] pc_id;                          // Program counter in ID stage
  logic [31:0] pc_wb;                          // Program counter in WB stage
  logic [33:0] imd_val_d_ex[2];                // Intermediate register for multicycle Ops
  logic [33:0] imd_val_q_ex[2];                // Intermediate register for multicycle Ops
  logic [1:0]  imd_val_we_ex;

  logic        data_ind_timing;
  logic        dummy_instr_en;
  logic [2:0]  dummy_instr_mask;
  logic        dummy_instr_seed_en;
  logic [31:0] dummy_instr_seed;
  logic        icache_enable;
  logic        icache_inval;
  logic        icache_ecc_error;
  logic        pc_mismatch_alert;
  logic        csr_shadow_err;

  logic        instr_first_cycle_id;
  logic        instr_valid_clear;
  logic        pc_set;
  logic        nt_branch_mispredict;
  logic [31:0] nt_branch_addr;
  pc_sel_e     pc_mux_id;                      // Mux selector for next PC
  exc_pc_sel_e exc_pc_mux_id;                  // Mux selector for exception PC
  exc_cause_t  exc_cause;                      // Exception cause

  logic        instr_intg_err;
  logic        lsu_load_err, lsu_load_err_raw;
  logic        lsu_store_err, lsu_store_err_raw;
  logic        lsu_load_resp_intg_err;
  logic        lsu_store_resp_intg_err;

  logic        expecting_load_resp_id;
  logic        expecting_store_resp_id;

  // LSU signals
  logic        lsu_addr_incr_req;
  logic [31:0] lsu_addr_last;

  // Jump and branch target and decision (EX->IF)
  logic [31:0] branch_target_ex;
  logic        branch_decision;

  // Core busy signals
  logic        ctrl_busy;
  logic        if_busy;
  logic        lsu_busy;

  // Register File
  logic [4:0]  rf_raddr_a;
  logic [31:0] rf_rdata_a;
  logic [4:0]  rf_raddr_b;
  logic [31:0] rf_rdata_b;
  logic        rf_ren_a;
  logic        rf_ren_b;
  logic [4:0]  rf_waddr_wb;
  logic [31:0] rf_wdata_wb;
  // Writeback register write data that can be used on the forwarding path (doesn't factor in memory
  // read data as this is too late for the forwarding path)
  logic [31:0] rf_wdata_fwd_wb;
  logic [31:0] rf_wdata_lsu;
  logic        rf_we_wb;
  logic        rf_we_lsu;
  logic        rf_ecc_err_comb;

  logic [4:0]  rf_waddr_id;
  logic [31:0] rf_wdata_id;
  logic        rf_we_id;
  logic        rf_rd_a_wb_match;
  logic        rf_rd_b_wb_match;

  // ALU Control
  alu_op_e     alu_operator_ex;
  logic [31:0] alu_operand_a_ex;
  logic [31:0] alu_operand_b_ex;

  logic [31:0] bt_a_operand;
  logic [31:0] bt_b_operand;

  logic [31:0] alu_adder_result_ex;    // Used to forward computed address to LSU
  logic [31:0] result_ex;

  // Multiplier Control
  logic        mult_en_ex;
  logic        div_en_ex;
  logic        mult_sel_ex;
  logic        div_sel_ex;
  md_op_e      multdiv_operator_ex;
  logic [1:0]  multdiv_signed_mode_ex;
  logic [31:0] multdiv_operand_a_ex;
  logic [31:0] multdiv_operand_b_ex;
  logic        multdiv_ready_id;

  // CSR control
  logic        csr_access;
  csr_op_e     csr_op;
  logic        csr_op_en;
  csr_num_e    csr_addr;
  logic [31:0] csr_rdata;
  logic [31:0] csr_wdata;
  logic        illegal_csr_insn_id;    // CSR access to non-existent register,
                                       // with wrong priviledge level,
                                       // or missing write permissions

  // Data Memory Control
  logic        lsu_we;
  logic [1:0]  lsu_type;
  logic        lsu_sign_ext;
  logic        lsu_req;
  logic        lsu_rdata_valid;
  logic [31:0] lsu_wdata;
  logic        lsu_req_done;

  // stall control
  logic        id_in_ready;
  logic        ex_valid;

  logic        lsu_resp_valid;
  logic        lsu_resp_err;

  // Signals between instruction core interface and pipe (if and id stages)
  logic        instr_req_int;          // Id stage asserts a req to instruction core interface
  logic        instr_req_gated;
  logic        instr_exec;

  // Writeback stage
  logic           en_wb;
  wb_instr_type_e instr_type_wb;
  logic           ready_wb;
  logic           rf_write_wb;
  logic           outstanding_load_wb;
  logic           outstanding_store_wb;
  logic           dummy_instr_wb;

  // Interrupts
  logic        nmi_mode;
  irqs_t       irqs;
  logic        csr_mstatus_mie;
  logic [31:0] csr_mepc, csr_depc;

  // PMP signals
  logic [33:0]  csr_pmp_addr [PMPNumRegions];
  pmp_cfg_t     csr_pmp_cfg  [PMPNumRegions];
  pmp_mseccfg_t csr_pmp_mseccfg;
  logic         pmp_req_err  [PMPNumChan];
  logic         data_req_out;

  logic        csr_save_if;
  logic        csr_save_id;
  logic        csr_save_wb;
  logic        csr_restore_mret_id;
  logic        csr_restore_dret_id;
  logic        csr_save_cause;
  logic        csr_mtvec_init;
  logic [31:0] csr_mtvec;
  logic [31:0] csr_mtval;
  logic        csr_mstatus_tw;
  priv_lvl_e   priv_mode_id;
  priv_lvl_e   priv_mode_lsu;

  // debug mode and dcsr configuration
  logic        debug_mode;
  logic        debug_mode_entering;
  dbg_cause_e  debug_cause;
  logic        debug_csr_save;
  logic        debug_single_step;
  logic        debug_ebreakm;
  logic        debug_ebreaku;
  logic        trigger_match;

  // signals relating to instruction movements between pipeline stages
  // used by performance counters and RVFI
  logic        instr_id_done;
  logic        instr_done_wb;

  logic        perf_instr_ret_wb;
  logic        perf_instr_ret_compressed_wb;
  logic        perf_instr_ret_wb_spec;
  logic        perf_instr_ret_compressed_wb_spec;
  logic        perf_iside_wait;
  logic        perf_dside_wait;
  logic        perf_mul_wait;
  logic        perf_div_wait;
  logic        perf_jump;
  logic        perf_branch;
  logic        perf_tbranch;
  logic        perf_load;
  logic        perf_store;

  // for RVFI
  logic        illegal_insn_id, unused_illegal_insn_id; // ID stage sees an illegal instruction

  // UPDATE
  // ID/Controller (n\u1ed1i gi\u1eefa ID và controller)
  logic ebrk_insn;
  logic mret_insn;
  logic dret_insn;
  logic ecall_insn;
  logic wfi_insn;
  logic jump_set;

  // ID/EX (n\u1ed1i gi\u1eefa ID và EX)
  logic [31:0] rf_rdata_a_ex;
  logic [31:0] rf_rdata_b_ex;
  
  rf_wd_sel_e rf_wdata_sel_ex;
  logic rf_we_ex;
  logic [4:0] rf_waddr_ex;

  imm_a_sel_e imm_a_mux_sel_ex;
  imm_b_sel_e imm_b_mux_sel_ex;

  logic [31:0] instr_ex;
  logic [4:0] instr_rs1_ex;
  logic [4:0] instr_rs2_ex;
  logic [4:0] instr_rs3_ex;
  logic [4:0] instr_rd_ex;
  logic [31:0] pc_ex;
  logic instr_is_compressed_ex;

  logic [31:0] imm_i_type_ex;
  logic [31:0] imm_b_type_ex;
  logic [31:0] imm_s_type_ex;
  logic [31:0] imm_j_type_ex;
  logic [31:0] imm_u_type_ex;
  logic [31:0] zimm_rs1_type_ex;

  op_a_sel_e         bt_a_mux_sel_EX;
  imm_b_sel_e        bt_b_mux_sel_EX;

  op_a_sel_e       alu_op_a_mux_sel_ex;
  op_b_sel_e       alu_op_b_mux_sel_ex;
  logic                    alu_instr_first_cycle_i;

  logic [1:0]            imd_val_we_o;
  logic [33:0]           imd_val_d_o[2];
  logic [33:0]           imd_val_q_i[2];

  logic [4:0] rf_waddr_ex_wb;
  logic [31:0] rf_wdata_ex_wb;
  logic rf_we_ex_wb;

  
  //////////////////////
  // Clock management //
  //////////////////////

  // Before going to sleep, wait for I- and D-side
  // interfaces to finish ongoing operations.
    // For non secure Ibex, synthesis is allowed to optimize core_busy_o.
    assign core_busy_o = (ctrl_busy || if_busy || lsu_busy) ? IbexMuBiOn : IbexMuBiOff;

  //////////////////////
  //     IF Stage     //
  //////////////////////

  IF_top #(
    .DmHaltAddr       (DmHaltAddr),
    .DmExceptionAddr  (DmExceptionAddr),
    .DummyInstructions(DummyInstructions),
    .ICache           (ICache),
    .ICacheECC        (ICacheECC),
    .BusSizeECC       (BusSizeECC),
    .TagSizeECC       (TagSizeECC),
    .LineSizeECC      (LineSizeECC),
    .PCIncrCheck      (PCIncrCheck),
    .ResetAll         (ResetAll),
    .RndCnstLfsrSeed  (RndCnstLfsrSeed),
    .RndCnstLfsrPerm  (RndCnstLfsrPerm),
    .BranchPredictor  (BranchPredictor),
    .MemECC           (MemECC),
    .MemDataWidth     (MemDataWidth)
  ) if_stage_i (
    .clk_i (clk_i),
    .rst_ni(rst_ni),

    .boot_addr_i(boot_addr_i),      // CONNECTED input core
    .req_i      (instr_req_gated),  // CONNECTED  assign \u1edf ngoài core vào instruction request control

    // instruction cache interface
    .instr_req_o       (instr_req_o),     // CONNECTED OUTPUT CORE
    .instr_addr_o      (instr_addr_o),    // CONNECTED OUTPUT CORE
    .instr_gnt_i       (instr_gnt_i),     // CONNECTED INPUT CORE
    .instr_rvalid_i    (instr_rvalid_i),  // CONNECTED INPUT CORE
    .instr_rdata_i     (instr_rdata_i),   // CONNECTED INPUT CORE
    .instr_bus_err_i   (instr_err_i),     // CONNECTED INPUT CORE
    .instr_intg_err_o  (instr_intg_err),  // CONNECTED (\u0111i\u1ec1u ki\u1ec7n cho alert_major_bus_o)

    // ICache RAM IO
    .ic_tag_req_o      (ic_tag_req_o),        // CONNECTED OUTPUT CORE
    .ic_tag_write_o    (ic_tag_write_o),      // CONNECTED OUTPUT CORE 
    .ic_tag_addr_o     (ic_tag_addr_o),       // CONNECTED OUTPUT CORE
    .ic_tag_wdata_o    (ic_tag_wdata_o),      // CONNECTED OUTPUT CORE
    .ic_tag_rdata_i    (ic_tag_rdata_i),      // CONNECTED INPUT CORE
    .ic_data_req_o     (ic_data_req_o),       // CONNECTED OUTPUT CORE
    .ic_data_write_o   (ic_data_write_o),     // CONNECTED OUTPUT CORE
    .ic_data_addr_o    (ic_data_addr_o),      // CONNECTED OUTPUT CORE
    .ic_data_wdata_o   (ic_data_wdata_o),     // CONNECTED OUTPUT CORE
    .ic_data_rdata_i   (ic_data_rdata_i),     // CONNECTED INPUT CORE
    .ic_scr_key_valid_i(ic_scr_key_valid_i),  // CONNECTED INPUT CORE
    .ic_scr_key_req_o  (ic_scr_key_req_o),    // NOT CONNECTED OUTPUT CORE (c\u1ea7n n\u1ed1i vào input cs_register)

    // control signals
    .instr_valid_clear_i   (instr_valid_clear),     // NOT CONNECTED (output t\u1eeb controller)
    .pc_set_i              (pc_set),                // NOT CONNECTED (output t\u1eeb controller)
    .pc_mux_i              (pc_mux_id),             // NOT CONNECTED (output t\u1eeb controller)
    .nt_branch_mispredict_i(nt_branch_mispredict),  // NOT CONNECTED (output t\u1eeb controller)

    .nt_branch_addr_i  (nt_branch_addr),     // NOT CONNECTED  (output t\u1eeb controller)     // not taken branch address in ID/EX

    .exc_pc_mux_i          (exc_pc_mux_id),   // NOT CONNECTED  (output t\u1eeb controller)
    .exc_cause             (exc_cause),       // NOT CONNECTED  (output t\u1eeb controller)

    .dummy_instr_en_i      (dummy_instr_en),      // UNUSED  (output t\u1eeb cs_register)
    .dummy_instr_mask_i    (dummy_instr_mask),    // UNUSED  (output t\u1eeb cs_register)
    .dummy_instr_seed_en_i (dummy_instr_seed_en), // UNUSED  (output t\u1eeb cs_register)
    .dummy_instr_seed_i    (dummy_instr_seed),    // UNUSED  (output t\u1eeb cs_register)

    .icache_enable_i       (icache_enable),       // NOT CONNECTED  (output t\u1eeb cs_register)
    .icache_inval_i        (icache_inval),        // CONNECTED ID
    .icache_ecc_error_o    (icache_ecc_error),    // CONNECTED (\u0111i\u1ec1u ki\u1ec7n cho alert_minor_o)

    // branch targets
    .branch_target_ex_i(branch_target_ex),        // NOT CONNECTED (t\u1eeb ex_stage)

    // CSRs
    .csr_mepc_i      (csr_mepc),        // NOT CONNECTED (t\u1eeb cs_register) // exception return address
    .csr_depc_i      (csr_depc),        // NOT CONNECTED (t\u1eeb cs_register) // debug return address
    .csr_mtvec_i     (csr_mtvec),       // NOT CONNECTED (t\u1eeb cs_register) // trap-vector base address
    .csr_mtvec_init_o(csr_mtvec_init),  // NOT CONNECTED (t\u1eeb cs_register)

    // pipeline stalls
    .id_in_ready_i(id_in_ready),    // NOT CONNECTED (output c\u1ee7a controller)

    // misc signals
    .pc_mismatch_alert_o(pc_mismatch_alert),    // NOT CONNECTED  (1 trong các \u0111i\u1ec1u ki\u1ec7n c\u1ee7a alert_major_internal_o)
    .if_busy_o          (if_busy),    // NOT CONNECTED  (1 trong các \u0111i\u1ec1u ki\u1ec7n cho core_busy_o)

    // outputs to ID stage
    .instr_valid_id_o        (instr_valid_id),      // CONNECTED ID  // instr in IF-ID is valid
    .instr_new_id_o          (instr_new_id),        // NOT CONNECTED (\u0111i\u1ec1u ki\u1ec7n cho \u0111\u1ed1ng RVFI) // instr in IF-ID is new
    .instr_rdata_id_o        (instr_rdata_id),      // CONNECTED ID  // instr for ID stage
    .instr_rdata_alu_id_o    (instr_rdata_alu_id),  // CONNECTED ID  // replicated instr for ID stage to reduce fan-out

    .instr_rdata_c_id_o      (instr_rdata_c_id),        // NOT CONNECTED (\u0111i vào input c\u1ee7a controller) // compressed instr for ID stage 
    .instr_is_compressed_id_o(instr_is_compressed_id),  // CONNECTED ID  (c\u1ea7n n\u1ed1i vào wb n\u1eefa)
    .instr_bp_taken_o        (instr_bp_taken_id),       // NOT CONNECTED (\u0111i vào input c\u1ee7a controller)
    .instr_fetch_err_o       (instr_fetch_err),         // CONNECTED ID
    .instr_fetch_err_plus2_o (instr_fetch_err_plus2),   // NOT CONNECTED (\u0111i vào input c\u1ee7a controller)
    .illegal_c_insn_id_o     (illegal_c_insn_id),       // CONNECTED ID
    
    .dummy_instr_id_o        (dummy_instr_id),          //UNUSED
    .pc_if_o                 (pc_if),                   // NOT CONNECTED (\u0111i vào input cs_register)
    .pc_id_o                 (pc_id),                   // CONNECTED ID  (\u0111i vào input cs_register)
    .pmp_err_if_i            (pmp_req_err[PMP_I]),      // NOT CONNECTED (output c\u1ee7a ibex_pmp)
    .pmp_err_if_plus2_i      (pmp_req_err[PMP_I2])     // NOT CONNECTED (output c\u1ee7a ibex_pmp)
  );

  // Core is waiting for the ISide when ID/EX stage is ready for a new instruction but none are
  // available
  assign perf_iside_wait = id_in_ready & ~instr_valid_id;

  // Multi-bit fetch enable used when SecureIbex == 1. When SecureIbex == 0 only use the bottom-bit
  // of fetch_enable_i. Ensure the multi-bit encoding has the bottom bit set for on and unset for
  // off so IbexMuBiOn/IbexMuBiOff can be used without needing to know the value of SecureIbex.

  // //`ASSERT_INIT(IbexMuBiSecureOnBottomBitSet,    IbexMuBiOn[0] == 1'b1)
  // //`ASSERT_INIT(IbexMuBiSecureOffBottomBitClear, IbexMuBiOff[0] == 1'b0)

  // fetch_enable_i can be used to stop the core fetching new instructions
    // For non secure Ibex only the bottom bit of fetch enable is considered
    logic unused_fetch_enable;
    assign unused_fetch_enable = ^fetch_enable_i[$bits(ibex_mubi_t)-1:1];

    assign instr_req_gated = instr_req_int & fetch_enable_i[0];
    assign instr_exec      = fetch_enable_i[0];


    logic jump_set_dec;

    logic branch_taken_id;


  //////////////////////
  //     ID Stage     //
  //////////////////////

  ID_top #(
    .RV32E          (RV32E),
    .RV32M          (RV32M),
    .RV32B          (RV32B),
    .BranchTargetALU(BranchTargetALU),
    .DataIndTiming  (DataIndTiming),
    .WritebackStage (WritebackStage),
    .BranchPredictor(BranchPredictor),
    .MemECC         (MemECC)
  ) id_stage_i (
    .clk_i (clk_i),
    .rst_ni(rst_ni),

    // Interface to IF stage
    .instr_valid_i          (instr_valid_id),           // CONNECTED (output t\u1eeb IF stage)
    .instr_fetch_err_i      (instr_fetch_err),          // CONNECTED (output t\u1eeb IF stage)
    .instr_rdata_i          (instr_rdata_id),           // CONNECTED (output t\u1eeb IF stage)   // from IF-ID pipeline registers
    .instr_rdata_alu_i      (instr_rdata_alu_id),       // CONNECTED (output t\u1eeb IF stage)   // from IF-ID pipeline registers
    .instr_is_compressed_i  (instr_is_compressed_id),   // CONNECTED (output t\u1eeb IF stage)
    .illegal_c_insn_i       (illegal_c_insn_id),        // CONNECTED (output t\u1eeb IF stage)
    .pc_id_i                (pc_id),                    // CONNECTED (output t\u1eeb IF stage)

    // Branch
    .instr_first_cycle_i     (instr_first_cycle_id),      // From FSM   // NOT DONE input logic
    .branch_taken_i          (branch_taken_id),      // From FSM   // NOT DONE input logic

    // LSU  Interface
    .lsu_req_EX           (lsu_req),  // to load store unit
    .lsu_we_EX            (lsu_we),  // to load store unit
    .lsu_type_EX          (lsu_type),  // to load store unit
    .lsu_sign_ext_EX      (lsu_sign_ext),  // to load store unit
    .lsu_wdata_EX         (lsu_wdata),  // to load store unit

    // MUL, DIV Interface
    .mult_en_EX            (mult_en_ex),    // CONNECTED (t\u1edbi input ex_stage)
    .div_en_EX             (div_en_ex),     // CONNECTED (t\u1edbi input ex_stage)
    .mult_sel_EX           (mult_sel_ex),   // CONNECTED (t\u1edbi input ex_stage)
    .div_sel_EX            (div_sel_ex),    // CONNECTED (t\u1edbi input ex_stage)
    .multdiv_operator_EX   (multdiv_operator_ex),     // CONNECTED (t\u1edbi input ex_stage)
    .multdiv_signed_mode_EX(multdiv_signed_mode_ex),  // CONNECTED (t\u1edbi input ex_stage)

    // CSR
    .csr_access_EX(csr_access),   // CONNECTED (t\u1edbi input ex_stage)
    .csr_op_EX(csr_op),           // CONNECTED (t\u1edbi input ex_stage)
    .csr_op_en_EX(csr_op_en),     // CONNECTED (t\u1edbi input ex_stage)

    // REG_FILE
    // read
    .rf_raddr_a_o      (rf_raddr_a),    // DONE (n\u1ed1i t\u1edbi REGISTER FILE FPGA)
    .rf_rdata_a_i      (rf_rdata_a),    // DONE (n\u1ed1i t\u1edbi REGISTER FILE FPGA)
    .rf_raddr_b_o      (rf_raddr_b),    // DONE (n\u1ed1i t\u1edbi REGISTER FILE FPGA)
    .rf_rdata_b_i      (rf_rdata_b),    // DONE (n\u1ed1i t\u1edbi REGISTER FILE FPGA)
    .rf_ren_a_o        (rf_ren_a),      // DONE (n\u1ed1i t\u1edbi REGISTER FILE FPGA)
    .rf_ren_b_o        (rf_ren_b),      // DONE (n\u1ed1i t\u1edbi REGISTER FILE FPGA)

    .rf_rdata_a_EX      (rf_rdata_a_ex),       // DONE (n\u1ed1i vào input ex_stage) output logic [31:0] 
    .rf_rdata_b_EX      (rf_rdata_b_ex),       // DONE (n\u1ed1i vào input ex_stage) output logic [31:0] 
    // write
    .rf_wdata_sel_EX    (rf_wdata_sel_ex),   // DONE (n\u1ed1i vào input ex_stage)output ibex_pkg::rf_wd_sel_e
    .rf_we_EX           (rf_we_ex),          // DONE (n\u1ed1i vào input ex_stage)output logic
    .rf_waddr_EX        (rf_waddr_ex),       // DONE (n\u1ed1i vào input ex_stage) output logic [4:0]

    // IMM
    .imm_a_mux_sel_EX   (imm_a_mux_sel_ex),   // DONE (n\u1ed1i vào input ex_stage)
    .imm_b_mux_sel_EX   (imm_b_mux_sel_ex),   // DONE (n\u1ed1i vào input ex_stage)

    .instr_EX               (instr_ex),                 // DONE output [31:0]
    .instr_rs1_EX           (instr_rs1_ex),             // DONE output [4:0]
    .instr_rs2_EX           (instr_rs2_ex),             // DONE output [4:0]
    .instr_rs3_EX           (instr_rs3_ex),             // DONE output [4:0]
    .instr_rd_EX            (instr_rd_ex),              // DONE output [4:0]
    .pc_EX                  (pc_ex),                    // DONE output [31:0]
    .instr_is_compressed_EX (instr_is_compressed_ex),   // DONE output logic
      
    .imm_i_type_EX          (imm_i_type_ex),   // DONE (n\u1ed1i vào input ex) output [31:0]
    .imm_b_type_EX          (imm_b_type_ex),   // DONE (n\u1ed1i vào input ex) output [31:0]
    .imm_s_type_EX          (imm_s_type_ex),   // DONE (n\u1ed1i vào input ex) output [31:0]
    .imm_j_type_EX          (imm_j_type_ex),   // DONE (n\u1ed1i vào input ex) output [31:0]
    .imm_u_type_EX          (imm_u_type_ex),   // DONE (n\u1ed1i vào input ex) output [31:0]
    .zimm_rs1_type_EX       (zimm_rs1_type_ex),   // DONE (n\u1ed1i vào input ex) output [31:0]
    
    // BTALU
    .bt_a_mux_sel_EX        (bt_a_mux_sel_EX),   // DONE (n\u1ed1i vào input ex_stage) output op_a_sel_e
    .bt_b_mux_sel_EX        (bt_b_mux_sel_EX),   // DONE (n\u1ed1i vào input ex_stage) output imm_b_sel_e
      
    // ALU
    .alu_operator_EX      (alu_operator_ex),     // NOT DONE output   alu_op_e
    .alu_op_a_mux_sel_EX  (alu_op_a_mux_sel_ex),     // DONE  output  op_a_sel_e
    .alu_op_b_mux_sel_EX  (alu_op_b_mux_sel_ex),     // DONE output  op_b_sel_e

    .mult_en_dec        (mult_en_dec),          // NOT DONE (n\u1ed1i vào input ex_stage)
    .div_en_dec         (div_en_dec),           // NOT DONE (n\u1ed1i vào input ex_stage)
    .lsu_we_dec         (lsu_we_dec),              // NOT DONE (n\u1ed1i vào input ex_stage)
    .lsu_req_dec        (lsu_req_dec),             // NOT DONE (n\u1ed1i vào input ex_stage)
    .rf_we_dec          (rf_we_dec),            // NOT DONE (n\u1ed1i vào input ex_stage)
    .branch_in_dec_o    (branch_in_dec),
    .jump_in_dec_o    (jump_in_dec),

    //.rf_ren_a_o       (rf_ren_a),            // NOT DONE (n\u1ed1i vào input ex_stage)
    
    // CONTROLLER INTERFACE
    .illegal_insn_o   (illegal_insn_dec),    // DONE (unused) output logic
    .ebrk_insn_o      (ebrk_insn),          // NOT DONE (n\u1ed1i vào controller) output logic
    .mret_insn_o      (mret_insn),          // NOT DONE (n\u1ed1i vào controller) output logic
                                              
    .dret_insn_o      (dret_insn),          // NOT DONE (n\u1ed1i vào controller) output logic
    .ecall_insn_o     (ecall_insn),         // NOT DONE (n\u1ed1i vào controller) output logic
    .wfi_insn_o       (wfi_insn),           // NOT DONE (n\u1ed1i vào controller) output logic
    .jump_set_o       (jump_set_dec),           // NOT DONE output logic
    .icache_inval_o   (icache_inval)        // DONE (n\u1ed1i input c\u1ee7a if_stage )
  );

  // for RVFI only
  assign unused_illegal_insn_id = illegal_insn_id;

  logic multdiv_en_dec;

  assign multdiv_en_dec   = mult_en_dec | div_en_dec;

  //////////////////////
  //     ID Stage     //
  //////////////////////
  ibex_fsm_control#(
    .BranchTargetALU(BranchTargetALU),
    .WritebackStage(WritebackStage),
    .BranchPredictor(BranchPredictor),
    .MemECC(MemECC)
  )fsm_control(
    .clk_i(clk_i),
    .rst_ni(rst_ni),

    .dret_insn_dec_i(dret_insn),  // NOT DONE (t\u1eeb output c\u1ee7a id_stage)
    //.debug_mode_o(debug_mode),    // NOT DONE (t\u1ee

    .mret_insn_dec_i(mret_insn),  // NOT DONE (t\u1eeb output c\u1ee7a id_stage)
    .csr_mstatus_tw_i(csr_mstatus_tw),  // NOT DONE (t\u1eeb output c\u1ee7a id_stage)
    .wfi_insn_dec_i(wfi_insn),    // NOT DONE (t\u1eeb output c\u1ee7a id_stage)

    .illegal_insn_o(illegal_insn_id),
    //.instr_valid_i(instr_valid_id),  // CONNECTED (t\u1eeb output c\u1ee7a if_stage)
    .illegal_insn_dec_i(illegal_insn_dec),  // NOT DONE (t\u1eeb output c\u1ee7a id_stage)
    .illegal_csr_insn_i(illegal_csr_insn_id),  // CONNECTED (t\u1eeb output c\u1ee7a if_stage)
    
    //.lsu_load_resp_intg_err_i(lsu_load_resp_intg_err),  // NOT DONE (t\u1eeb output c\u1ee7a ex_stage)
    //.lsu_store_resp_intg_err_i(lsu_store_resp_intg_err),  // NOT DONE (t\u1eeb output c\u1ee7a ex_stage)
    
    .ecall_insn_dec_i(ecall_insn),  // NOT DONE (t\u1eeb output c\u1ee7a id_stage)
    .ebrk_insn_i(ebrk_insn),  // NOT DONE (t\u1eeb output c\u1ee7a id_stage)
    .csr_pipe_flush_i(csr_pipe_flush),  // NOT DONE (t\u1eeb output c\u1ee7a id_stage)

    .instr_valid_i(instr_valid_id),  // CONNECTED (t\u1eeb output c\u1ee7a if_stage)
    .instr_rdata_i(instr_rdata_id),  // CONNECTED (t\u1eeb output c\u1ee7a if_stage)
    .instr_rdata_c_i(instr_rdata_c_id),  // NOT DONE (t\u1eeb output c\u1ee7a if_stage)
    .instr_is_compressed_i(instr_is_compressed_id),  // CONNECTED (t\u1eeb output c\u1ee7a if_stage)
    .instr_bp_taken_i(instr_bp_taken_id),  // NOT DONE (t\u1eeb output c\u1ee7a if_stage)
    .instr_fetch_err_i(instr_fetch_err),  // CONNECTED (t\u1eeb output c\u1ee7a if_stage)
    .instr_fetch_err_plus2_i(instr_fetch_err_plus2),  // NOT DONE (t\u1eeb output c\u1ee7a if_stage)

    .pc_id_i(pc_id),  // CONNECTED (t\u1eeb output c\u1ee7a if_stage)

    //.instr_valid_clear_o(instr_valid_clear),  // NOT DONE (t\u1eeb output c\u1ee7a ex_stage)
    .id_in_ready_o(id_in_ready),  // NOT DONE (t\u1eeb output c\u1ee7a ex_stage)
    .instr_exec_i(instr_exec),  // CONNECTED (t\u1eeb output c\u1ee7a if_stage)

    .instr_req_o(instr_req_int),  // CONNECTED (t\u1eeb output c\u1ee7a if_stage)
    .pc_set_o(pc_set),  // NOT DONE (t\u1eeb output c\u1ee7a ex_stage)
    .pc_mux_o(pc_mux_id),  // NOT DONE (t\u1eeb output c\u1ee7a ex_stage)
    .nt_branch_mispredict_o(nt_branch_mispredict),  // NOT DONE (t\u1eeb output c\u1ee7a ex_stage)
    //.nt_branch_addr_o(nt_branch_addr),  // NOT DONE (t\u1eeb output c\u1ee7a ex_stage)
    .exc_pc_mux_o(exc_pc_mux_id),  // NOT DONE (t\u1eeb output c\u1ee7a ex_stage)
    .exc_cause_o(exc_cause),  // NOT DONE (t\u1eeb output c\u1ee7a ex_stage)
    .instr_first_cycle_id_o(instr_first_cycle_id),  // NOT DONE (t\u1eeb output c\u1ee7a ex_stage)
    .instr_valid_clear_o(instr_valid_clear),  // NOT DONE (t\u1eeb output c\u1ee7a ex_stage)

    .lsu_addr_last_i(lsu_addr_last),  // NOT DONE (t\u1eeb output c\u1ee7a ex_stage)
    .lsu_load_err_i(lsu_load_err),  // NOT DONE (t\u1eeb output c\u1ee7a ex_stage)
    .lsu_load_resp_intg_err_i(lsu_load_resp_intg_err),  // NOT DONE (t\u1eeb output c\u1ee7a ex_stage)
    .lsu_store_err_i(lsu_store_err),  // NOT DONE (t\u1eeb output c\u1ee7a ex_stage)
    .lsu_store_resp_intg_err_i(lsu_store_resp_intg_err),  // NOT DONE (t\u1eeb output c\u1ee7a ex_stage)

    //.branch_in_dec_i(branch_in_dec),  // NOT DONE (t\u1eeb output c\u1ee7a ex_stage)
    .jump_in_dec_i(jump_in_dec),  // NOT DONE (t\u1eeb output c\u1ee7a ex_stage)
    
    .csr_mstatus_mie_i(csr_mstatus_mie),  // NOT DONE (t\u1eeb output c\u1ee7a ex_stage)
    .irq_pending_i(irq_pending),  // NOT DONE (t\u1eeb output c\u1ee7a ex_stage)
    .irqs_i(irqs),  // NOT DONE (t\u1eeb output c\u1ee7a ex_stage)
    .irq_nm_i(irq_nm),  // NOT DONE (t\u1eeb output c\u1ee7a ex_stage)
    .nmi_mode_o(nmi_mode),  // NOT DONE (t\u1eeb output c\u1ee7a ex_stage)

    .expecting_load_resp_o(expecting_load_resp),  // NOT DONE (t\u1eeb output c\u1ee7a ex_stage)
    .expecting_store_resp_o(expecting_store_resp),  // NOT DONE (t\u1eeb output c\u1ee7a ex_stage)

    .debug_mode_o(debug_mode),  // NOT DONE (t\u1eeb output c\u1ee7a ex_stage)
    .debug_mode_entering_o(debug_mode_entering),  // NOT DONE (t\u1eeb output c\u1ee7a ex_stage)
    .debug_cause_o(debug_cause),  // NOT DONE (t\u1eeb output c\u1ee7a ex_stage)
    .debug_csr_save_o(debug_csr_save),  // NOT DONE (t\u1eeb output c\u1ee7a ex_stage)
    .debug_req_i(debug_req),  // NOT DONE (t\u1eeb output c\u1ee7a ex_stage)
    .debug_single_step_i(debug_single_step),  // NOT DONE (t\u1eeb output c\u1ee7a ex_stage)
    .debug_ebreakm_i(debug_ebreakm),  // NOT DONE (t\u1eeb output c\u1ee7a ex_stage)
    .debug_ebreaku_i(debug_ebreaku),  // NOT DONE (t\u1eeb output c\u1ee7a ex_stage)
    .trigger_match_i(trigger_match),  // NOT DONE (t\u1eeb output c\u1ee7a ex_stage)

    .perf_branch_o(perf_branch),  // CONNECTED (t\u1eeb output c\u1ee7a ex_stage)
    .perf_jump_o(perf_jump),  // CONNECTED (t\u1eeb output c\u1ee7a ex_stage)
    .perf_tbranch_o(perf_tbranch),  // CONNECTED (t\u1eeb output c\u1ee7a ex_stage)

    .branch_taken_o(branch_taken_id),  // NOT DONE (t\u1eeb output c\u1ee7a ex_stage)
    .nt_branch_addr_o(nt_branch_addr),  // NOT DONE (t\u1eeb output c\u1ee7a ex_stage)

    .rf_we_raw_o(rf_we_raw),  // NOT DONE (t\u1eeb output c\u1ee7a ex_stage)
    .lsu_req_dec_i(lsu_req_dec),  // NOT DONE (t\u1eeb output c\u1ee7a ex_stage)
    .lsu_req_done_i(lsu_req_done),  // NOT DONE (t\u1eeb output c\u1ee7a ex_stage)
    .multdiv_en_dec_i(multdiv_en_dec),  // NOT DONE (t\u1eeb output c\u1ee7a ex_stage)
    .branch_in_dec_i(branch_in_dec),  // NOT DONE (t\u1eeb output c\u1ee7a ex_stage)
    .data_ind_timing_i(data_ind_timing),  // NOT DONE (t\u1eeb output c\u1ee7a ex_stage)
    .branch_decision_i(branch_decision),  // NOT DONE (t\u1eeb output c\u1ee7a ex_stage)

    .jump_set_dec_i(jump_set_dec),  // NOT DONE (t\u1eeb output c\u1ee7a ex_stage)
    .alu_multicycle_dec_i(alu_multicycle_dec),  // NOT DONE (t\u1eeb output c\u1ee7a ex_stage)

    .ready_wb_i(1),  // NOT DONE (t\u1eeb output c\u1ee7a ex_stage) ready_wb wait 
    .multdiv_ready_id_o(multdiv_ready_id),  // NOT DONE (t\u1eeb output c\u1ee7a ex_stage)
    .instr_id_done_o(instr_id_done),  // NOT DONE (t\u1eeb output c\u1ee7a ex_stage)
    .instr_type_wb_o(instr_type_wb),  // NOT DONE (t\u1eeb output c\u1ee7a ex_stage)

    .perf_dside_wait_o(perf_dside_wait),  // NOT DONE (t\u1eeb output c\u1ee7a ex_stage)
    .perf_mul_wait_o(perf_mul_wait),  // NOT DONE (t\u1eeb output c\u1ee7a ex_stage)
    .perf_div_wait_o(perf_div_wait),  // NOT DONE (t\u1eeb output c\u1ee7a ex_stage)

    //from lsu
    .lsu_resp_valid_i(lsu_resp_valid),  // NOT DONE (t\u1eeb output c\u1ee7a ex_stage)

    .priv_mode_id_i(priv_mode_id),  // NOT DONE (t\u1eeb output c\u1ee7a ex_stage)

    //decoder
    .mult_en_dec(mult_en_dec),  // NOT DONE (t\u1eeb output c\u1ee7a ex_stage)
    .div_en_dec(div_en_dec),  // NOT DONE (t\u1eeb output c\u1ee7a ex_stage)
    .lsu_we(lsu_we),  // NOT DONE (t\u1eeb output c\u1ee7a ex_stage)
    .rf_we_dec(rf_we_dec),  // NOT DONE (t\u1eeb output c\u1ee7a ex_stage)

    .rf_ren_a_i(rf_ren_a),  // NOT DONE (t\u1eeb output c\u1ee7a ex_stage)
    .rf_ren_b_i(rf_ren_b),  // NOT DONE (t\u1eeb output c\u1ee7a ex_stage)

    .rf_waddr_wb_i(rf_waddr_wb),  // NOT DONE (t\u1eeb output c\u1ee7a ex_stage)

    .rf_raddr_a_i(rf_raddr_a),  // NOT DONE (t\u1eeb output c\u1ee7a ex_stage)
    .rf_raddr_b_i(rf_raddr_b),  // NOT DONE (t\u1eeb output c\u1ee7a ex_stage)
    
    .ex_valid_i(ex_valid),  // CONNECTED (t\u1eeb output c\u1ee7a id_stage)

    .en_wb_o(en_wb)  // NOT DONE (t\u1eeb output c\u1ee7a ex_stage)



  );

  ///////////////////
  //    EX Stage   //
  ///////////////////

  

  EX_top ex_stage_i (
    .clk_i(clk_i),
    .rst_ni(rst_ni),

    // CSR RDATA
    .csr_rdata_i        (csr_rdata),  // NOT DONE (output t\u1eeb cs_register)

    // LSU inputs
    .lsu_addr_incr_req_i  (lsu_addr_incr_req),  // NOT DONE (output t\u1eeb load store unit)
    .lsu_addr_last_i      (lsu_addr_last),      // NOT DONE (output t\u1eeb load store unit)

    // ID/EX PIPELINE INPUT
    // MUL, DIV INTERFACE
    .mult_en_EX             (mult_en_ex),    // CONNECTED (t\u1eeb output c\u1ee7a id_stage)
    .div_en_EX              (div_en_ex),     // CONNECTED (t\u1eeb output c\u1ee7a id_stage)
    .mult_sel_EX            (mult_sel_ex),   // CONNECTED (t\u1eeb output c\u1ee7a id_stage)
    .div_sel_EX             (div_sel_ex),    // CONNECTED (t\u1eeb output c\u1ee7a id_stage)
    .multdiv_operator_EX    (multdiv_operator_ex),    // CONNECTED (t\u1eeb output c\u1ee7a id_stage)
    .multdiv_signed_mode_EX (multdiv_signed_mode_ex), // CONNECTED (t\u1eeb output c\u1ee7a id_stage)

    .multdiv_ready_id_i   (multdiv_ready_id),   // NOT DONE ( t\u1eeb FSM )
    .data_ind_timing_i    (data_ind_timing),   // NOT DONE ( t\u1eeb FSM )

    // CSR
    .csr_access_EX(csr_access),  // CONNECTED (t\u1eeb output c\u1ee7a id_stage)
    .csr_op_EX(csr_op),          // CONNECTED (t\u1eeb output c\u1ee7a id_stage)
    .csr_op_en_EX(csr_op_en),    // CONNECTED (t\u1eeb output c\u1ee7a id_stage)

    .rf_rdata_a_EX    (rf_rdata_a_ex),  // DONE (n\u1ed1i t\u1eeb output id_stage)
    .rf_rdata_b_EX    (rf_rdata_b_ex),  // DONE (n\u1ed1i t\u1eeb output id_stage)

    // WRITE
    .rf_wdata_sel_EX  (rf_wdata_sel_ex),  // CONNECTED (t\u1eeb output c\u1ee7a id_stage)
    .rf_we_EX         (rf_we_ex),                // CONNECTED (t\u1eeb output c\u1ee7a id_stage)
    .rf_waddr_EX      (rf_waddr_ex),          // CONNECTED (t\u1eeb output c\u1ee7a id_stage)

    // IMM
    .imm_a_mux_sel_EX (imm_a_mux_sel_ex),   // DONE (t\u1eeb output c\u1ee7a id_stage)
    .imm_b_mux_sel_EX (imm_b_mux_sel_ex),  // DONE (t\u1eeb output c\u1ee7a id_stage)

    .instr_EX       (instr_ex),                         // DONE (t\u1eeb output c\u1ee7a id_stage)
    .instr_rs1_EX   (instr_rs1_ex),                     // DONE (t\u1eeb output c\u1ee7a id_stage)
    .instr_rs2_EX   (instr_rs2_ex),                     // DONE (t\u1eeb output c\u1ee7a id_stage)
    .instr_rs3_EX   (instr_rs3_ex),                     // DONE (t\u1eeb output c\u1ee7a id_stage)
    .instr_rd_EX    (instr_rd_ex),                      // DONE (t\u1eeb output c\u1ee7a id_stage)
    .pc_EX          (pc_ex),                            // DONE (t\u1eeb output c\u1ee7a id_stage)
    .instr_is_compressed_EX (instr_is_compressed_ex),   // DONE (t\u1eeb output c\u1ee7a id_stage)

    .imm_i_type_EX    (imm_i_type_ex),      // DONE (t\u1eeb output c\u1ee7a id_stage)
    .imm_b_type_EX    (imm_b_type_ex),      // DONE (t\u1eeb output c\u1ee7a id_stage)
    .imm_s_type_EX    (imm_s_type_ex),      // DONE (t\u1eeb output c\u1ee7a id_stage)
    .imm_j_type_EX    (imm_j_type_ex),      // DONE (t\u1eeb output c\u1ee7a id_stage)
    .imm_u_type_EX    (imm_u_type_ex),      // DONE (t\u1eeb output c\u1ee7a id_stage)
    .zimm_rs1_type_EX (zimm_rs1_type_ex),   // DONE (t\u1eeb output c\u1ee7a id_stage)

    // BTALU
    .bt_a_mux_sel_EX(bt_a_mux_sel_EX),      // DONE (t\u1eeb output id_stage)
    .bt_b_mux_sel_EX(bt_b_mux_sel_EX),      // DONE (t\u1eeb output id_stage)

    // ALU
    .alu_operator_EX(alu_operator_ex),
    .alu_op_a_mux_sel_EX(alu_op_a_mux_sel_ex),
    .alu_op_b_mux_sel_EX(alu_op_b_mux_sel_ex),
    .alu_instr_first_cycle_i(instr_first_cycle_id),  // NOT DONE (t\u1eeb output c\u1ee7a id_stage)

    // intermediate val reg
    // .imd_val_we_o(imd_val_we_ex),    // NOT DONE () //to FSM
    // .imd_val_d_o(),     // NOT DONE ()
    // .imd_val_q_i(),     // NOT DONE ()

    // Outputs
    .alu_adder_result_ex_o(alu_adder_result_ex),
    .branch_target_o(branch_target_ex),
    .branch_decision_o(branch_decision),

    .ex_valid_o(ex_valid),  // NOT DONE (output t\u1eeb FSM)

    .rf_waddr_EX_o(rf_waddr_ex_wb),
    .rf_wdata_EX_o(rf_wdata_ex_wb),
    .rf_we_EX_o(rf_we_ex_wb)

  );

  /////////////////////
  // Load/store unit //
  /////////////////////
  assign data_req_o   = data_req_out & ~pmp_req_err[PMP_D];
  assign lsu_resp_err = lsu_load_err | lsu_store_err;

  LSU_top #(
    .MemDataWidth      (MemDataWidth),
    .MemECC         (MemECC)
  ) lsu_block_i (
    .clk_i(clk_i),
    .rst_ni(rst_ni),

    //data interface
    .data_req_o(data_req_out),
    .data_gnt_i(data_gnt_i),
    .data_rvalid_i(data_rvalid_i),
    .data_bus_err_i(data_err_i),
    .data_pmp_err_i(pmp_req_err[PMP_D]),

    .data_addr_o(data_addr_o),
    .data_wdata_o(data_wdata_o),
    .data_rdata_i(data_rdata_i),
    .data_we_o(data_we_o),
    .data_be_o(data_be_o),

    // signal to/from ID stage
    .lsu_we_i(lsu_we), //From ID
    .lsu_type_i(lsu_type), //from ID
    .lsu_wdata_i(lsu_wdata), //from FW data
    .lsu_sign_ext_i(lsu_sign_ext), //from ID

    .lsu_rdata_o(rf_wdata_lsu), //to WB
    .lsu_rdata_valid_o(lsu_rdata_valid), //to WB
    .lsu_req_i(lsu_req), //from id
    .lsu_req_done_o(lsu_req_done), //to FSM

    .adder_result_ex_i(alu_adder_result_ex), //from EX

    .addr_incr_req_o(lsu_addr_incr_req), //to EX
    .addr_last_o(lsu_addr_last), //to EX

    .lsu_resp_valid_o(lsu_resp_valid), //to FSM
    //
    //exception signals
    .load_err_o(lsu_load_err),
    .load_resp_intg_err_o(lsu_load_resp_intg_err),
    .store_err_o(lsu_store_err),
    .store_resp_intg_err_o(lsu_store_resp_intg_err),

    .busy_o(lsu_busy),

    .perf_load_o(perf_load),
    .perf_store_o(perf_store)
  );


  WB_top wb_stage_i(
    .clk_i (clk_i),
    .rst_ni(rst_ni),

    .rf_waddr_EX    (rf_waddr_ex_wb),    // CONNECTED (t\u1eeb output c\u1ee7a ex_stage)
    .rf_wdata_EX    (rf_wdata_ex_wb),    // CONNECTED (t\u1eeb output c\u1ee7a ex_stage)
    .rf_we_EX       (rf_we_ex_wb),       // CONNECTED (t\u1eeb output c\u1ee7a ex_stage)

    .rf_wdata_lsu_i (rf_wdata_lsu),   // CONNECTED (t\u1eeb output c\u1ee7a load store unit)
    .rf_we_lsu_i    (rf_we_lsu),      // CONNECTED (t\u1eeb output c\u1ee7a load store unit)

    .rf_waddr_WB_o  (rf_waddr_wb),    // CONNECTED (t\u1edbi input c\u1ee7a regfile)
    .rf_wdata_WB_o  (rf_wdata_wb),    // CONNECTED (t\u1edbi input c\u1ee7a regfile)
    .rf_we_WB_o     (rf_we_wb)      // CONNECTED (t\u1edbi input c\u1ee7a regfile)
    
  );

    // For non-secure configurations trust the bus protocol is being followed and we'll only ever
    // see a response if we have an outstanding request.
    //assign lsu_load_err  = lsu_load_err_raw;
    //assign lsu_store_err = lsu_store_err_raw;
    assign rf_we_lsu     = lsu_rdata_valid;

    // expected_load_resp_id/expected_store_resp_id signals are only used to guard against false
    // responses so they are unused in non-secure configurations
    logic unused_expecting_load_resp_id;
    logic unused_expecting_store_resp_id;

    assign unused_expecting_load_resp_id  = expecting_load_resp_id;
    assign unused_expecting_store_resp_id = expecting_store_resp_id;

  // chuy\u1ec3n rf vào trong regfile
  // assign dummy_instr_id_o = dummy_instr_id; n\u1ed1i tín hi\u1ec7u m\u1eb7c \u0111\u1ecbnh 0
  // assign dummy_instr_wb_o = dummy_instr_wb; n\u1ed1i tín hi\u1ec7u m\u1eb7c \u0111\u1ecbnh 0
  // assign rf_raddr_a_o     = rf_raddr_a;
  // assign rf_waddr_wb_o    = rf_waddr_wb;
  // assign rf_we_wb_o       = rf_we_wb;
  // assign rf_raddr_b_o     = rf_raddr_b;    

    logic unused_rf_ren_a, unused_rf_ren_b;
    logic unused_rf_rd_a_wb_match, unused_rf_rd_b_wb_match;

    assign unused_rf_ren_a         = rf_ren_a;
    assign unused_rf_ren_b         = rf_ren_b;
    assign unused_rf_rd_a_wb_match = rf_rd_a_wb_match;
    assign unused_rf_rd_b_wb_match = rf_rd_b_wb_match;
    assign rf_wdata_wb_ecc       = rf_wdata_wb;
    //assign rf_rdata_a              = rf_rdata_a_ecc_i;
    //assign rf_rdata_b              = rf_rdata_b_ecc_i;
    assign rf_ecc_err_comb         = 1'b0;

  ///////////////////////
  // Crash dump output //
  ///////////////////////

  logic [31:0] crash_dump_mtval;
  assign crash_dump_o.current_pc     = pc_id;
  assign crash_dump_o.next_pc        = pc_if;
  assign crash_dump_o.last_data_addr = lsu_addr_last;
  assign crash_dump_o.exception_pc   = csr_mepc;
  assign crash_dump_o.exception_addr = crash_dump_mtval;

`ifdef INC_ASSERT
  // Signals used for assertions only
  //logic outstanding_load_resp;
  //logic outstanding_store_resp;

  //logic outstanding_load_id;
  //logic outstanding_store_id;

  //assign outstanding_load_id  = id_stage_i.instr_executing & id_stage_i.lsu_req_dec &
  //                              ~id_stage_i.lsu_we;
  //assign outstanding_store_id = id_stage_i.instr_executing & id_stage_i.lsu_req_dec &
  //                              id_stage_i.lsu_we;

  //if (WritebackStage) begin : gen_wb_stage
    // When the writeback stage is present a load/store could be in ID or WB. A Load/store in ID can
    // see a response before it moves to WB when it is unaligned otherwise we should only see
    // a response when load/store is in WB.
  //  assign outstanding_load_resp  = outstanding_load_wb |
  //    (outstanding_load_id  & load_store_unit_i.split_misaligned_access);

  //  assign outstanding_store_resp = outstanding_store_wb |
  //    (outstanding_store_id & load_store_unit_i.split_misaligned_access);

    // When writing back the result of a load, the load must have made it to writeback
  //  //`ASSERT(NoMemRFWriteWithoutPendingLoad, rf_we_lsu |-> outstanding_load_wb, clk_i, !rst_ni)
  // end else begin : gen_no_wb_stage
  //   // Without writeback stage only look into whether load or store is in ID to determine if
  //   // a response is expected.
  //   assign outstanding_load_resp  = outstanding_load_id;
  //   assign outstanding_store_resp = outstanding_store_id;

  //   //`ASSERT(NoMemRFWriteWithoutPendingLoad, rf_we_lsu |-> outstanding_load_id, clk_i, !rst_ni)
  // end

  ////`ASSERT(NoMemResponseWithoutPendingAccess,
   // data_rvalid_i |-> outstanding_load_resp | outstanding_store_resp, clk_i, !rst_ni)


  // Keep track of the PC last seen in the ID stage when fetch is disabled
  logic [31:0]   pc_at_fetch_disable;
  ibex_mubi_t    last_fetch_enable;

  always_ff @(posedge clk_i or negedge rst_ni) begin
    if (!rst_ni) begin
      pc_at_fetch_disable <= '0;
      last_fetch_enable   <= '0;
    end else begin
      last_fetch_enable <= fetch_enable_i;

      if ((fetch_enable_i != IbexMuBiOn) && (last_fetch_enable == IbexMuBiOn)) begin
        pc_at_fetch_disable <= pc_id;
      end
    end
  end

  // When fetch is disabled no instructions should be executed. Once fetch is disabled either the
  // ID/EX stage is not valid or the PC of the ID/EX stage must remain as it was at disable. The
  // ID/EX valid should not ressert once it has been cleared.
  //`ASSERT(NoExecWhenFetchEnableNotOn, fetch_enable_i != IbexMuBiOn |=>
    // (~instr_valid_id || (pc_id == pc_at_fetch_disable)) && ~$rose(instr_valid_id))

  `endif


  ///////////////////
  // Alert outputs //
  ///////////////////

  // Minor alert - core is in a recoverable state
  assign alert_minor_o = icache_ecc_error;

    // Major internal alert - core is unrecoverable
  assign alert_major_internal_o = rf_ecc_err_comb | pc_mismatch_alert | csr_shadow_err;
  // Major bus alert
  assign alert_major_bus_o = lsu_load_resp_intg_err | lsu_store_resp_intg_err | instr_intg_err;

  ////////////////////////
  // RF (Register File) //
  ////////////////////////
  ibex_register_file_fpga #(
    .RV32E          (RV32E),
    .DataWidth      (MemDataWidth),
    .DummyInstructions(0),
    .WrenCheck      (0),
    .RdataMuxCheck  (0),
    .WordZeroVal    ('0)
  ) rf_i (
    .clk_i(clk_i),
    .rst_ni(rst_ni),

    .test_en_i(test_en_i), //from top, b? sung thêm vào core
    .dummy_instr_id_i(dummy_instr_id), //
    .dummy_instr_wb_i(dummy_instr_wb), //

    .raddr_a_i(rf_raddr_a),
    .rdata_a_o(rf_rdata_a),

    .raddr_b_i(rf_raddr_b),
    .rdata_b_o(rf_rdata_b),

    .waddr_a_i(rf_waddr_wb),
    .wdata_a_i(rf_wdata_wb),
    .we_a_i(rf_we_wb),

    .err_o ()
  );


  // //////////////////////
  // //  RVFI Interface  //
  // //////////////////////

  // // 4 stage pipeline requires 3 set (instr_info -> ex -> wb)
  // localparam int RVFI_STAGES = 3;

  // logic        rvfi_instr_new_wb;
  // logic        rvfi_intr_d;
  // logic        rvfi_intr_q;
  // logic        rvfi_set_trap_pc_d;
  // logic        rvfi_set_trap_pc_q;
  // logic [31:0] rvfi_insn_id;
  // logic [4:0]  rvfi_rs1_addr_d;
  // logic [4:0]  rvfi_rs1_addr_q;
  // logic [4:0]  rvfi_rs2_addr_d;
  // logic [4:0]  rvfi_rs2_addr_q;
  // logic [4:0]  rvfi_rs3_addr_d;
  // logic [31:0] rvfi_rs1_data_d;
  // logic [31:0] rvfi_rs1_data_q;
  // logic [31:0] rvfi_rs2_data_d;
  // logic [31:0] rvfi_rs2_data_q;
  // logic [31:0] rvfi_rs3_data_d;
  // logic [4:0]  rvfi_rd_addr_wb;
  // logic [4:0]  rvfi_rd_addr_q;
  // logic [4:0]  rvfi_rd_addr_d;
  // logic [31:0] rvfi_rd_wdata_wb;
  // logic [31:0] rvfi_rd_wdata_d;
  // logic [31:0] rvfi_rd_wdata_q;
  // logic        rvfi_rd_we_wb;
  // logic [3:0]  rvfi_mem_mask_int;
  // logic [31:0] rvfi_mem_rdata_d;
  // logic [31:0] rvfi_mem_rdata_q;
  // logic [31:0] rvfi_mem_wdata_d;
  // logic [31:0] rvfi_mem_wdata_q;
  // logic [31:0] rvfi_mem_addr_d;
  // logic [31:0] rvfi_mem_addr_q;
  // logic        rvfi_trap_id;
  // logic        rvfi_trap_wb;
  // logic        rvfi_irq_valid;
  // logic [63:0] rvfi_stage_order_d;
  // logic        rvfi_id_done;
  // logic        rvfi_wb_done;

  // logic            new_debug_req;
  // logic            new_nmi;
  // logic            new_nmi_int;
  // logic            new_irq;
  // ibex_pkg::irqs_t captured_mip;
  // logic            captured_nmi;
  // logic            captured_nmi_int;
  // logic            captured_debug_req;
  // logic            captured_valid;

  // // RVFI extension for co-simulation support
  // // debug_req and MIP captured at IF -> ID transition so one extra stage
  // ibex_pkg::irqs_t rvfi_ext_stage_pre_mip          [RVFI_STAGES+1];
  // ibex_pkg::irqs_t rvfi_ext_stage_post_mip         [RVFI_STAGES];
  // logic            rvfi_ext_stage_nmi              [RVFI_STAGES+1];
  // logic            rvfi_ext_stage_nmi_int          [RVFI_STAGES+1];
  // logic            rvfi_ext_stage_debug_req        [RVFI_STAGES+1];
  // logic            rvfi_ext_stage_debug_mode       [RVFI_STAGES];
  // logic [63:0]     rvfi_ext_stage_mcycle           [RVFI_STAGES];
  // logic [31:0]     rvfi_ext_stage_mhpmcounters     [RVFI_STAGES][10];
  // logic [31:0]     rvfi_ext_stage_mhpmcountersh    [RVFI_STAGES][10];
  // logic            rvfi_ext_stage_ic_scr_key_valid [RVFI_STAGES];
  // logic            rvfi_ext_stage_irq_valid        [RVFI_STAGES+1];


  // logic        rvfi_stage_valid_d   [RVFI_STAGES];

  // logic        rvfi_stage_valid     [RVFI_STAGES];
  // logic [63:0] rvfi_stage_order     [RVFI_STAGES];
  // logic [31:0] rvfi_stage_insn      [RVFI_STAGES];
  // logic        rvfi_stage_trap      [RVFI_STAGES];
  // logic        rvfi_stage_halt      [RVFI_STAGES];
  // logic        rvfi_stage_intr      [RVFI_STAGES];
  // logic [ 1:0] rvfi_stage_mode      [RVFI_STAGES];
  // logic [ 1:0] rvfi_stage_ixl       [RVFI_STAGES];
  // logic [ 4:0] rvfi_stage_rs1_addr  [RVFI_STAGES];
  // logic [ 4:0] rvfi_stage_rs2_addr  [RVFI_STAGES];
  // logic [ 4:0] rvfi_stage_rs3_addr  [RVFI_STAGES];
  // logic [31:0] rvfi_stage_rs1_rdata [RVFI_STAGES];
  // logic [31:0] rvfi_stage_rs2_rdata [RVFI_STAGES];
  // logic [31:0] rvfi_stage_rs3_rdata [RVFI_STAGES];
  // logic [ 4:0] rvfi_stage_rd_addr   [RVFI_STAGES];
  // logic [31:0] rvfi_stage_rd_wdata  [RVFI_STAGES];
  // logic [31:0] rvfi_stage_pc_rdata  [RVFI_STAGES];
  // logic [31:0] rvfi_stage_pc_wdata  [RVFI_STAGES];
  // logic [31:0] rvfi_stage_mem_addr  [RVFI_STAGES];
  // logic [ 3:0] rvfi_stage_mem_rmask [RVFI_STAGES];
  // logic [ 3:0] rvfi_stage_mem_wmask [RVFI_STAGES];
  // logic [31:0] rvfi_stage_mem_rdata [RVFI_STAGES];
  // logic [31:0] rvfi_stage_mem_wdata [RVFI_STAGES];

  // assign rvfi_valid     = rst_ni; //rvfi_stage_valid    [RVFI_STAGES-1];
  // assign rvfi_order     = 64'hFFFFFFFF; //rvfi_stage_order    [RVFI_STAGES-1];
  // assign rvfi_insn      = instr_rdata_id; //rvfi_stage_insn     [RVFI_STAGES-1];
  // assign rvfi_trap      = 1'b0; //rvfi_stage_trap     [RVFI_STAGES-1];
  // assign rvfi_halt      = 1'b0; //rvfi_stage_halt     [RVFI_STAGES-1];
  // assign rvfi_intr      = 1'b0; //rvfi_stage_intr     [RVFI_STAGES-1];
  // assign rvfi_mode      = 2'b0; //rvfi_stage_mode     [RVFI_STAGES-1];
  // assign rvfi_ixl       = 2'd1;  //rvfi_stage_ixl      [RVFI_STAGES-1];
  // assign rvfi_rs1_addr  = rvfi_stage_rs1_addr [RVFI_STAGES-1];
  // assign rvfi_rs2_addr  = rvfi_stage_rs2_addr [RVFI_STAGES-1];
  // assign rvfi_rs3_addr  = rvfi_stage_rs3_addr [RVFI_STAGES-1];
  // assign rvfi_rs1_rdata = rvfi_stage_rs1_rdata[RVFI_STAGES-1];
  // assign rvfi_rs2_rdata = rvfi_stage_rs2_rdata[RVFI_STAGES-1];
  // assign rvfi_rs3_rdata = rvfi_stage_rs3_rdata[RVFI_STAGES-1];
  // assign rvfi_rd_addr   = rvfi_stage_rd_addr  [RVFI_STAGES-1];
  // assign rvfi_rd_wdata  = rvfi_stage_rd_wdata [RVFI_STAGES-1];
  // assign rvfi_pc_rdata  = rvfi_stage_pc_rdata [RVFI_STAGES-1];
  // assign rvfi_pc_wdata  = rvfi_stage_pc_wdata [RVFI_STAGES-1];
  // assign rvfi_mem_addr  = rvfi_stage_mem_addr [RVFI_STAGES-1];
  // assign rvfi_mem_rmask = rvfi_stage_mem_rmask[RVFI_STAGES-1];
  // assign rvfi_mem_wmask = rvfi_stage_mem_wmask[RVFI_STAGES-1];
  // assign rvfi_mem_rdata = rvfi_stage_mem_rdata[RVFI_STAGES-1];
  // assign rvfi_mem_wdata = rvfi_stage_mem_wdata[RVFI_STAGES-1];

/////////////////////////////////////
/// Control and Status Registers////
//////////////////////////////////

  assign csr_wdata  = alu_operand_a_ex;
  assign csr_addr   = csr_num_e'(csr_access ? alu_operand_b_ex[11:0] : 12'b0);

ibex_cs_registers #(
    .DbgTriggerEn     (DbgTriggerEn),  
    .DbgHwBreakNum    (DbgHwBreakNum), 
    .DataIndTiming    (DataIndTiming), 
    .DummyInstructions(DummyInstructions), 
    .ShadowCSR        (ShadowCSR),         
    .ICache           (ICache),
    .MHPMCounterNum   (MHPMCounterNum),
    .MHPMCounterWidth (MHPMCounterWidth),
    .PMPEnable        (PMPEnable),
    .PMPGranularity   (PMPGranularity),
    .PMPNumRegions    (PMPNumRegions),
    .RV32E            (RV32E),
    .RV32M            (RV32M),
    .RV32B            (RV32B)
  ) cs_registers_i (
    .clk_i (clk_i),
    .rst_ni(rst_ni),

    // Hart ID from outside
    .hart_id_i      (hart_id_i),
    .priv_mode_id_o (priv_mode_id),
    .priv_mode_lsu_o(priv_mode_lsu),

    // mtvec
    .csr_mtvec_o     (csr_mtvec),
    .csr_mtvec_init_i(csr_mtvec_init),
    .boot_addr_i     (boot_addr_i),

    // Interface to CSRs     ( SRAM like)
    .csr_access_i(csr_access),
    .csr_addr_i  (csr_addr),
    .csr_wdata_i (csr_wdata),
    .csr_op_i    (csr_op),
    .csr_op_en_i (csr_op_en),
    .csr_rdata_o (csr_rdata),

    // Interrupt related control signals
    .irq_software_i   (irq_software_i),
    .irq_timer_i      (irq_timer_i),
    .irq_external_i   (irq_external_i),
    .irq_fast_i       (irq_fast_i),
    .nmi_mode_i       (nmi_mode),
    .irq_pending_o    (irq_pending_o),
    .irqs_o           (irqs),
    .csr_mstatus_mie_o(csr_mstatus_mie),
    .csr_mstatus_tw_o (csr_mstatus_tw),
    .csr_mepc_o       (csr_mepc),
    .csr_mtval_o      (crash_dump_mtval),

    // PMP
    .csr_pmp_cfg_o    (csr_pmp_cfg),
    .csr_pmp_addr_o   (csr_pmp_addr),
    .csr_pmp_mseccfg_o(csr_pmp_mseccfg),

    // debug
    .csr_depc_o           (csr_depc),
    .debug_mode_i         (debug_mode),
    .debug_mode_entering_i(debug_mode_entering),
    .debug_cause_i        (debug_cause),
    .debug_csr_save_i     (debug_csr_save),
    .debug_single_step_o  (debug_single_step),
    .debug_ebreakm_o      (debug_ebreakm),
    .debug_ebreaku_o      (debug_ebreaku),
    .trigger_match_o      (trigger_match),

    .pc_if_i(pc_if),
    .pc_id_i(pc_id),
    .pc_wb_i(pc_wb),

    .data_ind_timing_o    (data_ind_timing),
    .dummy_instr_en_o     (dummy_instr_en),
    .dummy_instr_mask_o   (dummy_instr_mask),
    .dummy_instr_seed_en_o(dummy_instr_seed_en),
    .dummy_instr_seed_o   (dummy_instr_seed),
    .icache_enable_o      (icache_enable),
    .csr_shadow_err_o     (csr_shadow_err),
    .ic_scr_key_valid_i   (ic_scr_key_valid_i),

    .csr_save_if_i     (csr_save_if),
    .csr_save_id_i     (csr_save_id),
    .csr_save_wb_i     (csr_save_wb),
    .csr_restore_mret_i(csr_restore_mret_id),
    .csr_restore_dret_i(csr_restore_dret_id),
    .csr_save_cause_i  (csr_save_cause),
    .csr_mcause_i      (exc_cause),
    .csr_mtval_i       (csr_mtval),
    .illegal_csr_insn_o(illegal_csr_insn_id)

    // .double_fault_seen_o,
  );

  `ifdef RVFI
  //////////////////////
  //  RVFI Interface  //
  //////////////////////
  // 4 stage pipeline requires 3 set (instr_info -> ex -> wb)
  localparam int RVFI_STAGES = 3;
  logic        rvfi_instr_new_wb;
  logic        rvfi_intr_d;
  logic        rvfi_intr_q;
  logic        rvfi_set_trap_pc_d;
  logic        rvfi_set_trap_pc_q;
  logic [31:0] rvfi_insn_id;
  logic [4:0]  rvfi_rs1_addr_d;
  logic [4:0]  rvfi_rs1_addr_q;
  logic [4:0]  rvfi_rs2_addr_d;
  logic [4:0]  rvfi_rs2_addr_q;
  logic [4:0]  rvfi_rs3_addr_d;
  logic [31:0] rvfi_rs1_data_d;
  logic [31:0] rvfi_rs1_data_q;
  logic [31:0] rvfi_rs2_data_d;
  logic [31:0] rvfi_rs2_data_q;
  logic [31:0] rvfi_rs3_data_d;
  logic [4:0]  rvfi_rd_addr_wb;
  logic [4:0]  rvfi_rd_addr_q;
  logic [4:0]  rvfi_rd_addr_d;
  logic [31:0] rvfi_rd_wdata_wb;
  logic [31:0] rvfi_rd_wdata_d;
  logic [31:0] rvfi_rd_wdata_q;
  logic        rvfi_rd_we_wb;
  logic [3:0]  rvfi_mem_mask_int;
  logic [31:0] rvfi_mem_rdata_d;
  logic [31:0] rvfi_mem_rdata_q;
  logic [31:0] rvfi_mem_wdata_d;
  logic [31:0] rvfi_mem_wdata_q;
  logic [31:0] rvfi_mem_addr_d;
  logic [31:0] rvfi_mem_addr_q;
  logic        rvfi_trap_id;
  logic        rvfi_trap_wb;
  logic        rvfi_irq_valid;
  logic [63:0] rvfi_stage_order_d;
  logic        rvfi_id_done;
  logic        rvfi_ex_done;
  logic        rvfi_wb_done;
  logic            new_debug_req;
  logic            new_nmi;
  logic            new_nmi_int;
  logic            new_irq;
  ibex_pkg::irqs_t captured_mip;
  logic            captured_nmi;
  logic            captured_nmi_int;
  logic            captured_debug_req;
  logic            captured_valid;
  // RVFI extension for co-simulation support
  // debug_req and MIP captured at IF -> ID transition so one extra stage
  ibex_pkg::irqs_t rvfi_ext_stage_pre_mip          [RVFI_STAGES+1];
  ibex_pkg::irqs_t rvfi_ext_stage_post_mip         [RVFI_STAGES];
  logic            rvfi_ext_stage_nmi              [RVFI_STAGES+1];
  logic            rvfi_ext_stage_nmi_int          [RVFI_STAGES+1];
  logic            rvfi_ext_stage_debug_req        [RVFI_STAGES+1];
  logic            rvfi_ext_stage_debug_mode       [RVFI_STAGES];
  logic [63:0]     rvfi_ext_stage_mcycle           [RVFI_STAGES];
  logic [31:0]     rvfi_ext_stage_mhpmcounters     [RVFI_STAGES][10];
  logic [31:0]     rvfi_ext_stage_mhpmcountersh    [RVFI_STAGES][10];
  logic            rvfi_ext_stage_ic_scr_key_valid [RVFI_STAGES];
  logic            rvfi_ext_stage_irq_valid        [RVFI_STAGES+1];
  logic        rvfi_stage_valid_d   [RVFI_STAGES];
  logic        rvfi_stage_valid     [RVFI_STAGES];
  logic [63:0] rvfi_stage_order     [RVFI_STAGES];
  logic [31:0] rvfi_stage_insn      [RVFI_STAGES];
  logic        rvfi_stage_trap      [RVFI_STAGES];
  logic        rvfi_stage_halt      [RVFI_STAGES];
  logic        rvfi_stage_intr      [RVFI_STAGES];
  logic [ 1:0] rvfi_stage_mode      [RVFI_STAGES];
  logic [ 1:0] rvfi_stage_ixl       [RVFI_STAGES];
  logic [ 4:0] rvfi_stage_rs1_addr  [RVFI_STAGES];
  logic [ 4:0] rvfi_stage_rs2_addr  [RVFI_STAGES];
  logic [ 4:0] rvfi_stage_rs3_addr  [RVFI_STAGES];
  logic [31:0] rvfi_stage_rs1_rdata [RVFI_STAGES];
  logic [31:0] rvfi_stage_rs2_rdata [RVFI_STAGES];
  logic [31:0] rvfi_stage_rs3_rdata [RVFI_STAGES];
  logic [ 4:0] rvfi_stage_rd_addr   [RVFI_STAGES];
  logic [31:0] rvfi_stage_rd_wdata  [RVFI_STAGES];
  logic [31:0] rvfi_stage_pc_rdata  [RVFI_STAGES];
  logic [31:0] rvfi_stage_pc_wdata  [RVFI_STAGES];
  logic [31:0] rvfi_stage_mem_addr  [RVFI_STAGES];
  logic [ 3:0] rvfi_stage_mem_rmask [RVFI_STAGES];
  logic [ 3:0] rvfi_stage_mem_wmask [RVFI_STAGES];
  logic [31:0] rvfi_stage_mem_rdata [RVFI_STAGES];
  logic [31:0] rvfi_stage_mem_wdata [RVFI_STAGES];
  assign rvfi_id_done = instr_id_done;
  assign rvfi_ex_done = ex_valid;
  assign rvfi_wb_done = rvfi_stage_valid[0] & (instr_done_wb | rvfi_stage_trap[0]);
  assign rvfi_rd_addr_wb  = rf_waddr_wb;
  assign rvfi_rd_wdata_wb = rf_we_wb ? rf_wdata_wb : rf_wdata_lsu;
  assign rvfi_rd_we_wb    = rf_we_wb | rf_we_lsu;
  // assign rvfi_stage_valid_d[0] = (rvfi_id_done & ~dummy_instr_id) | (rvfi_stage_valid[0] & ~rvfi_wb_done);
  assign rvfi_stage_valid_d[0] = (rvfi_id_done);
  assign rvfi_stage_valid_d[1] = (rvfi_ex_done);
  assign rvfi_stage_valid_d[RVFI_STAGES-1] = rvfi_wb_done;
  // Memory address/write data available first cycle of ld/st instruction from register read
  always_comb begin
    if (instr_first_cycle_id) begin   // Need to check
      rvfi_mem_addr_d  = alu_adder_result_ex;
      rvfi_mem_wdata_d = lsu_wdata;
    end else begin
      rvfi_mem_addr_d  = rvfi_mem_addr_q;
      rvfi_mem_wdata_d = rvfi_mem_wdata_q;
    end
  end
  // Capture read data from LSU when it becomes valid
  always_comb begin
    if (lsu_resp_valid) begin   // Need to check
      rvfi_mem_rdata_d = rf_wdata_lsu;
    end else begin
      rvfi_mem_rdata_d = rvfi_mem_rdata_q;
    end
  end
  always_ff @(posedge clk_i or negedge rst_ni) begin    // Need to check
    if (!rst_ni) begin
      rvfi_mem_addr_q  <= '0;
      rvfi_mem_rdata_q <= '0;
      rvfi_mem_wdata_q <= '0;
    end else begin
      rvfi_mem_addr_q  <= rvfi_mem_addr_d;
      rvfi_mem_rdata_q <= rvfi_mem_rdata_d;
      rvfi_mem_wdata_q <= rvfi_mem_wdata_d;
    end
  end
  // Byte enable based on data type
  always_comb begin     // Need to check
    unique case (lsu_type)
      2'b00:   rvfi_mem_mask_int = 4'b1111;
      2'b01:   rvfi_mem_mask_int = 4'b0011;
      2'b10:   rvfi_mem_mask_int = 4'b0001;
      default: rvfi_mem_mask_int = 4'b0000;
    endcase
  end
  always_comb begin     // Need to check
    if (instr_is_compressed_id) begin
      rvfi_insn_id = {16'b0, instr_rdata_c_id};
    end else begin
      rvfi_insn_id = instr_rdata_id;
    end
  end
  // NEED SIGNAL WB_DONE form wb_stage
  // rvfi_valid
  logic instr_done_wb_1;
  // rvfi_insn
  logic [31:0] rvfi_insn_id_1;
  logic [31:0] rvfi_insn_id_2;
  logic [31:0] rvfi_insn_id_3;
  // rvfi_pc_rdata
  logic [31:0] pc_id_1;
  logic [31:0] pc_id_2;
  logic [31:0] pc_if_1;
  logic [31:0] pc_if_2;
  //rvfi_pc_wdata
  logic [31:0] pc_wdata;
  assign pc_wdata = pc_set ? branch_target_ex : pc_if;
  logic [31:0] pc_wdata_1;
  logic [31:0] pc_wdata_2;
  logic [31:0] pc_wdata_3;
  //rvfi_mem_rmask
  logic [4:0] rvfi_mem_rmask_int_1;
  logic [4:0] rvfi_mem_rmask_int_2;
  //rvfi_mem_wmask
  logic [4:0] rvfi_mem_wmask_int_1;
  logic [4:0] rvfi_mem_wmask_int_2;
    
  // rvfi_pc_rdata
  always @(posedge clk_i or negedge rst_ni) begin
    if(~rst_ni) begin
      instr_done_wb_1 <= 0;
      instr_done_wb <= 0;
      rvfi_insn_id_1 <= 0;
      rvfi_insn_id_2 <= 0;
      rvfi_insn_id_3 <= 0;
      pc_id_1 <= 0;
      pc_id_2 <= 0;
      pc_if_1 <= 0;
      pc_if_2 <= 0;
      pc_wdata_1 <= 0;
      pc_wdata_2 <= 0;
      pc_wdata_3 <= 0;
      rvfi_mem_rmask_int_1 <= 0;
      rvfi_mem_rmask_int_2 <= 0;
      rvfi_mem_wmask_int_1 <= 0;
      rvfi_mem_wmask_int_2 <= 0;
    end else begin
      instr_done_wb <= rf_we_wb;
      instr_done_wb_1 <= instr_done_wb;
      rvfi_insn_id_1 <= rvfi_insn_id;
      rvfi_insn_id_2 <= rvfi_insn_id_1;
      rvfi_insn_id_3 <= rvfi_insn_id_2;
      pc_id_1 <= pc_id;
      pc_id_2 <= pc_id_1;
      pc_if_1 <= pc_if;
      pc_if_2 <= pc_if_1;
      pc_wdata_1 <= pc_wdata;
      pc_wdata_2 <= pc_wdata_1;
      pc_wdata_3 <= pc_wdata_2;
      rvfi_mem_rmask_int_1 <= rvfi_mem_mask_int;
      rvfi_mem_rmask_int_2 <= rvfi_mem_rmask_int_1;
      rvfi_mem_wmask_int_1 <= data_we_o ? rvfi_mem_mask_int : 4'b0000;;
      rvfi_mem_wmask_int_2 <= rvfi_mem_wmask_int_1;
    end
  end
  
  // Source registers 1 and 2 are read in the first instruction cycle
  // Source register 3 is read in the second instruction cycle.
  always_comb begin
    if (instr_first_cycle_id) begin   // Need to check
      rvfi_rs1_data_d = rf_ren_a ? rf_rdata_a_ex : '0;
      rvfi_rs1_addr_d = rf_ren_a ? rf_raddr_a : '0;
      rvfi_rs2_data_d = rf_ren_b ? rf_rdata_b_ex : '0;
      rvfi_rs2_addr_d = rf_ren_b ? rf_raddr_b : '0;
      rvfi_rs3_data_d = '0;
      rvfi_rs3_addr_d = '0;
    end else begin
      rvfi_rs1_data_d = rvfi_rs1_data_q;
      rvfi_rs1_addr_d = rvfi_rs1_addr_q;
      rvfi_rs2_data_d = rvfi_rs2_data_q;
      rvfi_rs2_addr_d = rvfi_rs2_addr_q;
      rvfi_rs3_data_d = rf_rdata_a_ex;
      rvfi_rs3_addr_d = rf_raddr_a;
    end
  end
  always_ff @(posedge clk_i or negedge rst_ni) begin
    if (!rst_ni) begin
      rvfi_rs1_data_q <= '0;
      rvfi_rs1_addr_q <= '0;
      rvfi_rs2_data_q <= '0;
      rvfi_rs2_addr_q <= '0;
    end else begin
      rvfi_rs1_data_q <= rvfi_rs1_data_d;
      rvfi_rs1_addr_q <= rvfi_rs1_addr_d;
      rvfi_rs2_data_q <= rvfi_rs2_data_d;
      rvfi_rs2_addr_q <= rvfi_rs2_addr_d;
    end
  end
  always_comb begin
    if (rvfi_rd_we_wb) begin
      // Capture address/data of write to register file
      rvfi_rd_addr_d = rvfi_rd_addr_wb;
      // If writing to x0 zero write data as required by RVFI specification
      if (rvfi_rd_addr_wb == 5'b0) begin
        rvfi_rd_wdata_d = '0;
      end else begin
        rvfi_rd_wdata_d = rvfi_rd_wdata_wb;
      end
    end else if (rvfi_instr_new_wb) begin
      // If no RF write but new instruction in Writeback (when present) or ID/EX (when no writeback
      // stage present) then zero RF write address/data as required by RVFI specification
      rvfi_rd_addr_d  = '0;
      rvfi_rd_wdata_d = '0;
    end else begin
      // Otherwise maintain previous value
      rvfi_rd_addr_d  = rvfi_rd_addr_q;
      rvfi_rd_wdata_d = rvfi_rd_wdata_q;
    end
  end
  // RD write register is refreshed only once per cycle and
  // then it is kept stable for the cycle.
  always_ff @(posedge clk_i or negedge rst_ni) begin
    if (!rst_ni) begin
      rvfi_rd_addr_q    <= '0;
      rvfi_rd_wdata_q   <= '0;
    end else begin
      rvfi_rd_addr_q    <= rvfi_rd_addr_d;
      rvfi_rd_wdata_q   <= rvfi_rd_wdata_d;
    end
  end
  logic rvfi_stage_rf_wr_suppress_wb;
  logic rvfi_rf_wr_suppress_wb;
  // Set when RF write from load data is suppressed due to an integrity error
  assign rvfi_rf_wr_suppress_wb =
    instr_done_wb & ~rf_we_wb & outstanding_load_wb & lsu_load_resp_intg_err;
  always@(posedge clk_i or negedge rst_ni) begin
    if (!rst_ni) begin
      rvfi_stage_rf_wr_suppress_wb <= 1'b0;
    end else if (rvfi_wb_done) begin
      rvfi_stage_rf_wr_suppress_wb <= rvfi_rf_wr_suppress_wb;
    end
  end
  assign rvfi_ext_rf_wr_suppress = rvfi_stage_rf_wr_suppress_wb;
  assign rvfi_intr_d = instr_first_cycle_id ? rvfi_set_trap_pc_q : rvfi_intr_q;
  always_comb begin
    rvfi_set_trap_pc_d = rvfi_set_trap_pc_q;
    if (pc_set && pc_mux_id == PC_EXC &&
        (exc_pc_mux_id == EXC_PC_EXC || exc_pc_mux_id == EXC_PC_IRQ)) begin
      // PC is set to enter a trap handler
      rvfi_set_trap_pc_d = 1'b1;
    end else if (rvfi_set_trap_pc_q && rvfi_id_done) begin
      // first instruction has been executed after PC is set to trap handler
      rvfi_set_trap_pc_d = 1'b0;
    end
  end
  always_ff @(posedge clk_i or negedge rst_ni) begin
    if (!rst_ni) begin
      rvfi_set_trap_pc_q <= 1'b0;
      rvfi_intr_q        <= 1'b0;
    end else begin
      rvfi_set_trap_pc_q <= rvfi_set_trap_pc_d;
      rvfi_intr_q        <= rvfi_intr_d;
    end
  end
/*
  for (genvar i = 0; i < RVFI_STAGES; i = i + 1) begin : g_rvfi_stages
    always_ff @(posedge clk_i or negedge rst_ni) begin
      if(!rst_ni) begin
        rvfi_stage_halt[i]                 <= '0;
        rvfi_stage_trap[i]                 <= '0;
        rvfi_stage_intr[i]                 <= '0;
        rvfi_stage_order[i]                <= '0;
        rvfi_stage_insn[i]                 <= '0;
        rvfi_stage_mode[i]                 <= {PRIV_LVL_M};
        rvfi_stage_ixl[i]                  <= CSR_MISA_MXL;
        rvfi_stage_rs1_addr[i]             <= '0;
        rvfi_stage_rs2_addr[i]             <= '0;
        rvfi_stage_rs3_addr[i]             <= '0;
        rvfi_stage_pc_rdata[i]             <= '0;
        rvfi_stage_pc_wdata[i]             <= '0;
        rvfi_stage_mem_rmask[i]            <= '0;
        rvfi_stage_mem_wmask[i]            <= '0;
        rvfi_stage_valid[i]                <= '0;
        rvfi_stage_rs1_rdata[i]            <= '0;
        rvfi_stage_rs2_rdata[i]            <= '0;
        rvfi_stage_rs3_rdata[i]            <= '0;
        rvfi_stage_rd_wdata[i]             <= '0;
        rvfi_stage_rd_addr[i]              <= '0;
        rvfi_stage_mem_rdata[i]            <= '0;
        rvfi_stage_mem_wdata[i]            <= '0;
        rvfi_stage_mem_addr[i]             <= '0;
        rvfi_ext_stage_pre_mip[i+1]        <= '0;
        rvfi_ext_stage_post_mip[i]         <= '0;
        rvfi_ext_stage_nmi[i+1]            <= '0;
        rvfi_ext_stage_nmi_int[i+1]        <= '0;
        rvfi_ext_stage_debug_req[i+1]      <= '0;
        rvfi_ext_stage_debug_mode[i]       <= '0;
        rvfi_ext_stage_mcycle[i]           <= '0;
        rvfi_ext_stage_mhpmcounters[i]     <= '{10{'0}};
        rvfi_ext_stage_mhpmcountersh[i]    <= '{10{'0}};
        rvfi_ext_stage_ic_scr_key_valid[i] <= '0;
      end else begin
        rvfi_stage_valid[i] <= rvfi_stage_valid_d[i];
        if (i == 0) begin
          if (rvfi_id_done) begin
            rvfi_stage_halt[i]                 <= '0;
            rvfi_stage_trap[i]                 <= rvfi_trap_id;
            rvfi_stage_intr[i]                 <= rvfi_intr_d;
            rvfi_stage_order[i]                <= rvfi_stage_order_d;
            rvfi_stage_insn[i]                 <= rvfi_insn_id;
            rvfi_stage_mode[i]                 <= {priv_mode_id};
            rvfi_stage_ixl[i]                  <= CSR_MISA_MXL;
            rvfi_stage_rs1_addr[i]             <= rvfi_rs1_addr_d;
            rvfi_stage_rs2_addr[i]             <= rvfi_rs2_addr_d;
            rvfi_stage_rs3_addr[i]             <= rvfi_rs3_addr_d;
            rvfi_stage_pc_rdata[i]             <= pc_id;
            rvfi_stage_pc_wdata[i]             <= pc_set ? branch_target_ex : pc_if;
            rvfi_stage_mem_rmask[i]            <= rvfi_mem_mask_int;
            rvfi_stage_mem_wmask[i]            <= data_we_o ? rvfi_mem_mask_int : 4'b0000;
            rvfi_stage_rs1_rdata[i]            <= rvfi_rs1_data_d;
            rvfi_stage_rs2_rdata[i]            <= rvfi_rs2_data_d;
            rvfi_stage_rs3_rdata[i]            <= rvfi_rs3_data_d;
            rvfi_stage_rd_addr[i]              <= rvfi_rd_addr_d;
            rvfi_stage_rd_wdata[i]             <= rvfi_rd_wdata_d;
            rvfi_stage_mem_rdata[i]            <= rvfi_mem_rdata_d;
            rvfi_stage_mem_wdata[i]            <= rvfi_mem_wdata_d;
            rvfi_stage_mem_addr[i]             <= rvfi_mem_addr_d;
            rvfi_ext_stage_debug_mode[i]       <= debug_mode;
            rvfi_ext_stage_mcycle[i]           <= cs_registers_i.mcycle_counter_i.counter_val_o;
            rvfi_ext_stage_ic_scr_key_valid[i] <= cs_registers_i.cpuctrlsts_ic_scr_key_valid_q;
            // This is done this way because SystemVerilog does not support looping through
            // gen_cntrs[k] within a for loop.
            for (int k=0; k < 10; k++) begin
              rvfi_ext_stage_mhpmcounters[i][k]  <= cs_registers_i.mhpmcounter[k+3][31:0];
              rvfi_ext_stage_mhpmcountersh[i][k] <= cs_registers_i.mhpmcounter[k+3][63:32];
            end
          end
          // Some of the rvfi_ext_* signals are used to provide an interrupt notification (signalled
          // via rvfi_ext_irq_valid) when there isn't a valid retired instruction as well as
          // providing information along with a retired instruction. Move these up the rvfi pipeline
          // for both cases.
          if (rvfi_id_done | rvfi_ext_stage_irq_valid[i]) begin
            rvfi_ext_stage_pre_mip[i+1]   <= rvfi_ext_stage_pre_mip[i];
            rvfi_ext_stage_post_mip[i]    <= cs_registers_i.mip;
            rvfi_ext_stage_nmi[i+1]       <= rvfi_ext_stage_nmi[i];
            rvfi_ext_stage_nmi_int[i+1]   <= rvfi_ext_stage_nmi_int[i];
            rvfi_ext_stage_debug_req[i+1] <= rvfi_ext_stage_debug_req[i];
          end
        end else begin
          if (rvfi_wb_done) begin
            rvfi_stage_halt[i]      <= rvfi_stage_halt[i-1];
            rvfi_stage_trap[i]      <= rvfi_stage_trap[i-1] | rvfi_trap_wb;
            rvfi_stage_intr[i]      <= rvfi_stage_intr[i-1];
            rvfi_stage_order[i]     <= rvfi_stage_order[i-1];
            rvfi_stage_insn[i]      <= rvfi_stage_insn[i-1];
            rvfi_stage_mode[i]      <= rvfi_stage_mode[i-1];
            rvfi_stage_ixl[i]       <= rvfi_stage_ixl[i-1];
            rvfi_stage_rs1_addr[i]  <= rvfi_stage_rs1_addr[i-1];
            rvfi_stage_rs2_addr[i]  <= rvfi_stage_rs2_addr[i-1];
            rvfi_stage_rs3_addr[i]  <= rvfi_stage_rs3_addr[i-1];
            rvfi_stage_pc_rdata[i]  <= rvfi_stage_pc_rdata[i-1];
            rvfi_stage_pc_wdata[i]  <= rvfi_stage_pc_wdata[i-1];
            rvfi_stage_mem_rmask[i] <= rvfi_stage_mem_rmask[i-1];
            rvfi_stage_mem_wmask[i] <= rvfi_stage_mem_wmask[i-1];
            rvfi_stage_rs1_rdata[i] <= rvfi_stage_rs1_rdata[i-1];
            rvfi_stage_rs2_rdata[i] <= rvfi_stage_rs2_rdata[i-1];
            rvfi_stage_rs3_rdata[i] <= rvfi_stage_rs3_rdata[i-1];
            rvfi_stage_mem_wdata[i] <= rvfi_stage_mem_wdata[i-1];
            rvfi_stage_mem_addr[i]  <= rvfi_stage_mem_addr[i-1];
            // For 2 RVFI_STAGES/Writeback Stage ignore first stage flops for rd_addr, rd_wdata and
            // mem_rdata. For RF write addr/data actual write happens in writeback so capture
            // address/data there. For mem_rdata that is only available from the writeback stage.
            // Previous stage flops still exist in RTL as they are used by the non writeback config
            rvfi_stage_rd_addr[i]   <= rvfi_rd_addr_d;
            rvfi_stage_rd_wdata[i]  <= rvfi_rd_wdata_d;
            rvfi_stage_mem_rdata[i] <= rvfi_mem_rdata_d;
            rvfi_ext_stage_debug_mode[i]       <= rvfi_ext_stage_debug_mode[i-1];
            rvfi_ext_stage_mcycle[i]           <= rvfi_ext_stage_mcycle[i-1];
            rvfi_ext_stage_ic_scr_key_valid[i] <= rvfi_ext_stage_ic_scr_key_valid[i-1];
            rvfi_ext_stage_mhpmcounters[i]     <= rvfi_ext_stage_mhpmcounters[i-1];
            rvfi_ext_stage_mhpmcountersh[i]    <= rvfi_ext_stage_mhpmcountersh[i-1];
          end
          // Some of the rvfi_ext_* signals are used to provide an interrupt notification (signalled
          // via rvfi_ext_irq_valid) when there isn't a valid retired instruction as well as
          // providing information along with a retired instruction. Move these up the rvfi pipeline
          // for both cases.
          if (rvfi_wb_done | rvfi_ext_stage_irq_valid[i]) begin
            rvfi_ext_stage_pre_mip[i+1]   <= rvfi_ext_stage_pre_mip[i];
            rvfi_ext_stage_post_mip[i]    <= rvfi_ext_stage_post_mip[i-1];
            rvfi_ext_stage_nmi[i+1]       <= rvfi_ext_stage_nmi[i];
            rvfi_ext_stage_nmi_int[i+1]   <= rvfi_ext_stage_nmi_int[i];
            rvfi_ext_stage_debug_req[i+1] <= rvfi_ext_stage_debug_req[i];
          end
        end
      end
    end
  end
*/
  assign rvfi_valid     = rvfi_wb_done;// instr_done_wb; //rvfi_stage_valid    [RVFI_STAGES-1];
  assign rvfi_order     = 64'hFFFFFFFF; //rvfi_stage_order    [RVFI_STAGES-1];
  assign rvfi_insn      = rvfi_insn_id_1; //rvfi_stage_intr    [RVFI_STAGES-1];
  assign rvfi_trap      = 1'b0;         //rvfi_stage_trap     [RVFI_STAGES-1];
  assign rvfi_halt      = 1'b0;         //rvfi_stage_halt     [RVFI_STAGES-1];
  assign rvfi_intr      = 1'b0;         //rvfi_stage_intr     [RVFI_STAGES-1];
  assign rvfi_mode      = 2'b01;        //rvfi_stage_mode     [RVFI_STAGES-1];
  assign rvfi_ixl       = 2'd1;         //rvfi_stage_ixl      [RVFI_STAGES-1];
  assign rvfi_rs1_addr  = rvfi_rs1_addr_d; //rvfi_stage_rs1_addr [RVFI_STAGES-1];
  assign rvfi_rs2_addr  = rvfi_rs2_addr_d; //rvfi_stage_rs2_addr [RVFI_STAGES-1];
  assign rvfi_rs3_addr  = rvfi_rs3_addr_d; //rvfi_stage_rs3_addr [RVFI_STAGES-1];
  assign rvfi_rs1_rdata = rvfi_rs1_data_d; //rvfi_stage_rs1_rdata[RVFI_STAGES-1];
  assign rvfi_rs2_rdata = rvfi_rs2_data_d; //rvfi_stage_rs2_rdata[RVFI_STAGES-1];
  assign rvfi_rs3_rdata = rvfi_rs3_data_d; //rvfi_stage_rs3_rdata[RVFI_STAGES-1];
  assign rvfi_rd_addr   = rvfi_rd_addr_d; //rvfi_stage_rd_addr  [RVFI_STAGES-1];
  assign rvfi_rd_wdata  = rvfi_rd_wdata_d; //rvfi_stage_rd_wdata [RVFI_STAGES-1];
  assign rvfi_pc_rdata  = pc_if; //rvfi_stage_pc_rdata [RVFI_STAGES-1];
  assign rvfi_pc_wdata  = pc_wdata; //rvfi_stage_pc_wdata [RVFI_STAGES-1];
  assign rvfi_mem_addr  = rvfi_mem_addr_d; //rvfi_stage_mem_addr [RVFI_STAGES-1];
  assign rvfi_mem_rmask = rvfi_mem_rmask_int_2; //rvfi_stage_mem_rmask[RVFI_STAGES-1];
  assign rvfi_mem_wmask = rvfi_mem_wmask_int_2; //rvfi_stage_mem_wmask[RVFI_STAGES-1];
  assign rvfi_mem_rdata = rvfi_mem_rdata_d; //rvfi_stage_mem_rdata[RVFI_STAGES-1];
  assign rvfi_mem_wdata = rvfi_mem_wdata_d; //rvfi_stage_mem_wdata[RVFI_STAGES-1];
`endif

    priv_lvl_e unused_priv_lvl_ls;
    logic [33:0] unused_csr_pmp_addr [PMPNumRegions];
    pmp_cfg_t    unused_csr_pmp_cfg  [PMPNumRegions];
    pmp_mseccfg_t unused_csr_pmp_mseccfg;
    assign unused_priv_lvl_ls = priv_mode_lsu;
    assign unused_csr_pmp_addr = csr_pmp_addr;
    assign unused_csr_pmp_cfg = csr_pmp_cfg;
    assign unused_csr_pmp_mseccfg = csr_pmp_mseccfg;

    // Output tieoff
    assign pmp_req_err[PMP_I]  = 1'b0;
    assign pmp_req_err[PMP_I2] = 1'b0;
    assign pmp_req_err[PMP_D]  = 1'b0;

  // Comment lai vi khong dung Performance Counters

    // performance counter related signals
  //   .instr_ret_i                (perf_instr_ret_wb),
  //   .instr_ret_compressed_i     (perf_instr_ret_compressed_wb),
  //   .instr_ret_spec_i           (perf_instr_ret_wb_spec),
  //   .instr_ret_compressed_spec_i(perf_instr_ret_compressed_wb_spec),
  //   .iside_wait_i               (perf_iside_wait),
  //   .jump_i                     (perf_jump),
  //   .branch_i                   (perf_branch),
  //   .branch_taken_i             (perf_tbranch),
  //   .mem_load_i                 (perf_load),
  //   .mem_store_i                (perf_store),
  //   .dside_wait_i               (perf_dside_wait),
  //   .mul_wait_i                 (perf_mul_wait),
  //   .div_wait_i                 (perf_div_wait)
  // );

  // Comment lai Assertion
  
  // These assertions are in top-level as instr_valid_id required as the enable term
  // //`ASSERT(IbexCsrOpValid, instr_valid_id |-> csr_op inside {
  //     CSR_OP_READ,
  //     CSR_OP_WRITE,
  //     CSR_OP_SET,
  //     CSR_OP_CLEAR
  //     })
  // //`ASSERT_KNOWN_IF(IbexCsrWdataIntKnown, cs_registers_i.csr_wdata_int, csr_op_en)

///  Comment lai vi khong dung module PMP
  // if (PMPEnable) begin : g_pmp
  //   logic [31:0] pc_if_inc;
  //   logic [33:0] pmp_req_addr [PMPNumChan];
  //   pmp_req_e    pmp_req_type [PMPNumChan];
  //   priv_lvl_e   pmp_priv_lvl [PMPNumChan];

  //   assign pc_if_inc            = pc_if + 32'd2;
  //   assign pmp_req_addr[PMP_I]  = {2'b00, pc_if};
  //   assign pmp_req_type[PMP_I]  = PMP_ACC_EXEC;
  //   assign pmp_priv_lvl[PMP_I]  = priv_mode_id;
  //   assign pmp_req_addr[PMP_I2] = {2'b00, pc_if_inc};
  //   assign pmp_req_type[PMP_I2] = PMP_ACC_EXEC;
  //   assign pmp_priv_lvl[PMP_I2] = priv_mode_id;
  //   assign pmp_req_addr[PMP_D]  = {2'b00, data_addr_o[31:0]};
  //   assign pmp_req_type[PMP_D]  = data_we_o ? PMP_ACC_WRITE : PMP_ACC_READ;
  //   assign pmp_priv_lvl[PMP_D]  = priv_mode_lsu;

endmodule
