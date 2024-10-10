module ibex_fsm_control# (
    parameter bit BranchTargetALU = 0,
    parameter bit WritebackStage  = 1'b0,
    parameter bit BranchPredictor = 1'b0,
    parameter bit MemECC          = 1'b0
)
(   
  input logic clk_i,
  input logic rst_ni,

  input logic dret_insn_dec_i,
  //output logic debug_mode_o,

  input logic mret_insn_dec_i,
  input logic csr_mstatus_tw_i,
  input logic wfi_insn_dec_i,

  output logic illegal_insn_o,
  //input logic instr_valid_i,
  input logic illegal_insn_dec_i,
  input logic illegal_csr_insn_i,

  //input logic lsu_load_resp_intg_err_i,
  //input logic lsu_store_resp_intg_err_i,

  input logic ecall_insn_dec_i,
  input logic ebrk_insn_i,
  input logic csr_pipe_flush_i,

  //IF/ID
  input  logic                      instr_valid_i,
  input  logic [31:0]               instr_rdata_i,         // from IF-ID pipeline registers
  input  logic [15:0]               instr_rdata_c_i,       // from IF-ID pipeline registers
  input  logic                      instr_is_compressed_i,
  input  logic                      instr_bp_taken_i,
  input  logic                      instr_fetch_err_i,
  input  logic                      instr_fetch_err_plus2_i,

  input  logic [31:0]               pc_id_i,

  //output logic                      instr_valid_clear_o,
  //output logic                      id_in_ready_o,
  output logic                      id_in_ready_o,         // ID stage is ready for next instr
  input  logic                      instr_exec_i,

  // IF and ID stage signals
  output logic                      instr_req_o,
  output logic                      pc_set_o,
  output ibex_pkg::pc_sel_e         pc_mux_o,
  output logic                      nt_branch_mispredict_o,
  //output logic [31:0]               nt_branch_addr_o,
  output ibex_pkg::exc_pc_sel_e     exc_pc_mux_o,
  output ibex_pkg::exc_cause_t      exc_cause_o,
  output logic                      instr_first_cycle_id_o,
  output logic                      instr_valid_clear_o,   // kill instr in IF-ID reg

  input  logic [31:0]               lsu_addr_last_i,
  input  logic                      lsu_load_err_i,
  input  logic                      lsu_load_resp_intg_err_i,
  input  logic                      lsu_store_err_i,
  input  logic                      lsu_store_resp_intg_err_i,

  //input logic branch_in_dec_i, //from decoder
  input logic jump_in_dec_i, //from decoder

  // Interrupt signals
  input  logic                      csr_mstatus_mie_i,
  input  logic                      irq_pending_i,
  input  ibex_pkg::irqs_t           irqs_i,
  input  logic                      irq_nm_i,
  output logic                      nmi_mode_o,

  output logic                      expecting_load_resp_o,
  output logic                      expecting_store_resp_o,

  // Debug Signal
  output logic                      debug_mode_o,
  output logic                      debug_mode_entering_o,
  output ibex_pkg::dbg_cause_e      debug_cause_o,
  output logic                      debug_csr_save_o,
  input  logic                      debug_req_i,
  input  logic                      debug_single_step_i,
  input  logic                      debug_ebreakm_i,
  input  logic                      debug_ebreaku_i,
  input  logic                      trigger_match_i,

  output logic perf_branch_o,
  output logic perf_jump_o,
  output logic perf_tbranch_o,

  output logic branch_taken_o, //to decoder
  output logic [31:0] nt_branch_addr_o,

  output logic rf_we_raw_o, //to id

  input logic lsu_req_dec_i,
  input logic lsu_req_done_i,
  input logic multdiv_en_dec_i,
  input logic branch_in_dec_i,
  input logic data_ind_timing_i,
  input logic branch_decision_i,

  input logic jump_set_dec_i,
  input logic alu_multicycle_dec_i,

  input logic ready_wb_i,
  output logic multdiv_ready_id_o,

  output logic instr_id_done_o,
  output logic instr_type_wb_o,

  output logic perf_dside_wait_o,
  output logic perf_mul_wait_o,
  output logic perf_div_wait_o,

  //from lsu
  input logic lsu_resp_valid_i,

  input ibex_pkg::priv_lvl_e  priv_mode_id_i,
  

  //from decoder
  input logic mult_en_dec, 
  input logic div_en_dec,
  input logic lsu_we,
  input logic rf_we_dec,

  input logic rf_ren_a_i,
  input logic rf_ren_b_i,

  input logic [4:0] rf_waddr_wb_i,

  input logic [4:0] rf_raddr_a_i,
  input logic [4:0] rf_raddr_b_i,
  
  input logic ex_valid_i,

  output logic en_wb_o
);

  logic        rf_we_raw;

  logic        stall_ld_hz;
  logic        stall_mem;
  logic        stall_multdiv;
  logic        stall_branch;
  logic        stall_jump;
  logic        stall_id;
  logic        stall_wb;
  logic        flush_id;
  logic        instr_done;
  logic        multicycle_done;

  logic        multdiv_en_dec;
  logic        alu_multicycle_dec;
  logic        jump_set_dec;
  logic        branch_in_dec;
  logic        lsu_req_dec;
  logic        lsu_req_done;

  assign        multdiv_en_dec = multdiv_en_dec_i;
  assign        alu_multicycle_dec=alu_multicycle_dec_i;
  assign        jump_set_dec = jump_set_dec_i;
  assign        branch_in_dec = branch_in_dec_i;
  assign        lsu_req_dec = lsu_req_dec_i;
  assign        lsu_req_done = lsu_req_done_i;

  logic        wb_exception;
  logic        id_exception;

  logic        branch_set, branch_set_raw, branch_set_raw_d;
  logic        branch_jump_set_done_q, branch_jump_set_done_d;
  logic        branch_not_set;
  logic        branch_taken;
  logic        jump_in_dec;
  assign        jump_in_dec = jump_in_dec_i;
  logic        jump_set, jump_set_raw;

  logic        illegal_dret_insn;
  logic        illegal_umode_insn;

  logic        dret_insn_dec;
  logic        mret_insn_dec;

  assign        dret_insn_dec = dret_insn_dec_i;
  assign        mret_insn_dec = mret_insn_dec_i;

  logic        wfi_insn_dec;
  logic        illegal_insn_dec;

  assign        wfi_insn_dec = wfi_insn_dec_i;
  assign        illegal_insn_dec = illegal_insn_dec_i;

  logic        mem_resp_intg_err;

  logic        ecall_insn_dec;

  logic        ebrk_insn;

  logic        csr_pipe_flush;

  assign        ecall_insn_dec = ecall_insn_dec_i;

  assign        ebrk_insn = ebrk_insn_i;

  assign        csr_pipe_flush = csr_pipe_flush_i;

  logic        controller_run;
  
  logic        stall_alu;

  logic	instr_executing;
  logic instr_executing_spec;



    import ibex_pkg::*;

  ////////////////
  // Controller //
  ////////////////

  // Executing DRET outside of Debug Mode causes an illegal instruction exception.
  assign illegal_dret_insn  = dret_insn_dec & ~debug_mode_o;
  // Some instructions can only be executed in M-Mode
  assign illegal_umode_insn = (priv_mode_id_i != PRIV_LVL_M) &
                              // MRET must be in M-Mode. TW means trap WFI to M-Mode.
                              (mret_insn_dec | (csr_mstatus_tw_i & wfi_insn_dec));

  assign illegal_insn_o = instr_valid_i &
      (illegal_insn_dec | illegal_csr_insn_i | illegal_dret_insn | illegal_umode_insn);

  assign mem_resp_intg_err = lsu_load_resp_intg_err_i | lsu_store_resp_intg_err_i;

  ibex_controller #(
    .WritebackStage (WritebackStage),
    .BranchPredictor(BranchPredictor)
  ) controller_i (
    .clk_i (clk_i),
    .rst_ni(rst_ni),

    .ctrl_busy_o(ctrl_busy_o),

    // decoder related signals
    .illegal_insn_i  (illegal_insn_o),
    .ecall_insn_i    (ecall_insn_dec),
    .mret_insn_i     (mret_insn_dec),
    .dret_insn_i     (dret_insn_dec),
    .wfi_insn_i      (wfi_insn_dec),
    .ebrk_insn_i     (ebrk_insn),
    .csr_pipe_flush_i(csr_pipe_flush),

    // from IF-ID pipeline
    .instr_valid_i          (instr_valid_i),
    .instr_i                (instr_rdata_i),
    .instr_compressed_i     (instr_rdata_c_i),
    .instr_is_compressed_i  (instr_is_compressed_i),
    .instr_bp_taken_i       (instr_bp_taken_i),
    .instr_fetch_err_i      (instr_fetch_err_i),
    .instr_fetch_err_plus2_i(instr_fetch_err_plus2_i),
    .pc_id_i                (pc_id_i),

    // to IF-ID pipeline
    .instr_valid_clear_o(instr_valid_clear_o),
    .id_in_ready_o      (id_in_ready_o),
    .controller_run_o   (controller_run),
    .instr_exec_i       (instr_exec_i),

    // to prefetcher
    .instr_req_o           (instr_req_o),
    .pc_set_o              (pc_set_o),
    .pc_mux_o              (pc_mux_o),
    .nt_branch_mispredict_o(nt_branch_mispredict_o),
    .exc_pc_mux_o          (exc_pc_mux_o),
    .exc_cause_o           (exc_cause_o),

    // LSU
    .lsu_addr_last_i    (lsu_addr_last_i),
    .load_err_i         (lsu_load_err_i),
    .mem_resp_intg_err_i(mem_resp_intg_err),
    .store_err_i        (lsu_store_err_i),
    .wb_exception_o     (wb_exception),
    .id_exception_o     (id_exception),

    // jump/branch control
    .branch_set_i     (branch_set),
    .branch_not_set_i (branch_not_set),
    .jump_set_i       (jump_set),

    // interrupt signals
    .csr_mstatus_mie_i(csr_mstatus_mie_i),
    .irq_pending_i    (irq_pending_i),
    .irqs_i           (irqs_i),
    .irq_nm_ext_i     (irq_nm_i),
    .nmi_mode_o       (nmi_mode_o),

    // CSR Controller Signals
    .csr_save_if_o        (csr_save_if_o),
    .csr_save_id_o        (csr_save_id_o),
    .csr_save_wb_o        (csr_save_wb_o),
    .csr_restore_mret_id_o(csr_restore_mret_id_o),
    .csr_restore_dret_id_o(csr_restore_dret_id_o),
    .csr_save_cause_o     (csr_save_cause_o),
    .csr_mtval_o          (csr_mtval_o),
    .priv_mode_i          (priv_mode_id_i),

    // Debug Signal
    .debug_mode_o         (debug_mode_o),
    .debug_mode_entering_o(debug_mode_entering_o),
    .debug_cause_o        (debug_cause_o),
    .debug_csr_save_o     (debug_csr_save_o),
    .debug_req_i          (debug_req_i),
    .debug_single_step_i  (debug_single_step_i),
    .debug_ebreakm_i      (debug_ebreakm_i),
    .debug_ebreaku_i      (debug_ebreaku_i),
    .trigger_match_i      (trigger_match_i),

    .stall_id_i(stall_id),
    .stall_wb_i(stall_wb),
    .flush_id_o(flush_id),
    .ready_wb_i(ready_wb_i),

    // Performance Counters
    .perf_jump_o   (perf_jump_o),
    .perf_tbranch_o(perf_tbranch_o)
  );


  ////////////////////////
  // Branch set control //
  ////////////////////////

  if (BranchTargetALU) begin : g_branch_set_direct
    // Branch set fed straight to controller with branch target ALU
    // (condition pass/fail used same cycle as generated instruction request)
    assign branch_set_raw      = branch_set_raw_d;
  end else begin : g_branch_set_flop
    // SEC_CM: CORE.DATA_REG_SW.SCA
    // Branch set flopped without branch target ALU, or in fixed time execution mode
    // (condition pass/fail used next cycle where branch target is calculated)
    logic branch_set_raw_q;

    always_ff @(posedge clk_i or negedge rst_ni) begin
      if (!rst_ni) begin
        branch_set_raw_q <= 1'b0;
      end else begin
        branch_set_raw_q <= branch_set_raw_d;
      end
    end

    // Branches always take two cycles in fixed time execution mode, with or without the branch
    // target ALU (to avoid a path from the branch decision into the branch target ALU operand
    // muxing).
    assign branch_set_raw      = (BranchTargetALU && !data_ind_timing_i) ? branch_set_raw_d :
                                                                           branch_set_raw_q;

  end

  // Track whether the current instruction in ID/EX has done a branch or jump set.
  assign branch_jump_set_done_d = (branch_set_raw | jump_set_raw | branch_jump_set_done_q) &
    ~instr_valid_clear_o;

  always_ff @(posedge clk_i or negedge rst_ni) begin
    if (!rst_ni) begin
      branch_jump_set_done_q <= 1'b0;
    end else begin
      branch_jump_set_done_q <= branch_jump_set_done_d;
    end
  end

  // the _raw signals from the state machine may be asserted for multiple cycles when
  // instr_executing_spec is asserted and instr_executing is not asserted. This may occur where
  // a memory error is seen or a there are outstanding memory accesses (indicate a load or store is
  // in the WB stage). The branch or jump speculatively begins the fetch but is held back from
  // completing until it is certain the outstanding access hasn't seen a memory error. This logic
  // ensures only the first cycle of a branch or jump set is sent to the controller to prevent
  // needless extra IF flushes and fetches.
  assign jump_set        = jump_set_raw        & ~branch_jump_set_done_q;
  assign branch_set      = branch_set_raw      & ~branch_jump_set_done_q;

  // Branch condition is calculated in the first cycle and flopped for use in the second cycle
  // (only used in fixed time execution mode to determine branch destination).
  // if (DataIndTiming) begin : g_sec_branch_taken
  //   // SEC_CM: CORE.DATA_REG_SW.SCA
  //   logic branch_taken_q;

  //   always_ff @(posedge clk_i or negedge rst_ni) begin
  //     if (!rst_ni) begin
  //       branch_taken_q <= 1'b0;
  //     end else begin
  //       branch_taken_q <= branch_decision_i;
  //     end
  //   end

  //   assign branch_taken = ~data_ind_timing_i | branch_taken_q;

  // end else begin : g_nosec_branch_taken

    // Signal unused without fixed time execution mode - only taken branches will trigger
    // branch_set_raw
    assign branch_taken = 1'b1;
    assign branch_taken_o = branch_taken;
  // end

  //////////////////////////////
  // Branch not-taken address //
  //////////////////////////////

  // if (BranchPredictor) begin : g_calc_nt_addr
  //   assign nt_branch_addr_o = pc_id_i + (instr_is_compressed_i ? 32'd2 : 32'd4);
  // end else begin : g_n_calc_nt_addr
    assign nt_branch_addr_o = 32'd0;
  // end

  ///////////////
  // ID-EX FSM //
  ///////////////

  //typedef enum logic { FIRST_CYCLE, MULTI_CYCLE } id_fsm_e;
//  id_fsm_e id_fsm_q, id_fsm_d;
//
//  always_ff @(posedge clk_i or negedge rst_ni) begin : id_pipeline_reg
//    if (!rst_ni) begin
//      id_fsm_q <= FIRST_CYCLE;
//    end else if (instr_executing) begin
//      id_fsm_q <= id_fsm_d;
//    end
//  end

//  assign rf_we_raw_o = rf_we_raw;

//  // ID/EX stage can be in two states, FIRST_CYCLE and MULTI_CYCLE. An instruction enters
//  // MULTI_CYCLE if it requires multiple cycles to complete regardless of stalls and other
//  // considerations. An instruction may be held in FIRST_CYCLE if it's unable to begin executing
//  // (this is controlled by instr_executing).

//  always_comb begin
//    id_fsm_d                = id_fsm_q;
//    rf_we_raw               = rf_we_dec;
//    stall_multdiv           = 1'b0;
//    stall_jump              = 1'b0;
//    stall_branch            = 1'b0;
//    stall_alu               = 1'b0;
//    branch_set_raw_d        = 1'b0;
//    branch_not_set          = 1'b0;
//    jump_set_raw            = 1'b0;
//    perf_branch_o           = 1'b0;

//    if (instr_executing_spec) begin
//      unique case (id_fsm_q)
//        FIRST_CYCLE: begin
//          unique case (1'b1)
//            lsu_req_dec: begin
//              if (!WritebackStage) begin
//                // LSU operation
//                id_fsm_d    = MULTI_CYCLE;
//              end else begin
//                if(~lsu_req_done_i) begin
//                  id_fsm_d  = MULTI_CYCLE;
//                end
//              end
//            end
//            multdiv_en_dec: begin
 //             // MUL or DIV operation
//              if (1) begin
 //               // When single-cycle multiply is configured mul can finish in the first cycle so
 //               // only enter MULTI_CYCLE state if a result isn't immediately available
 //               id_fsm_d      = MULTI_CYCLE;
 //               rf_we_raw     = 1'b0;
 //               stall_multdiv = 1'b1;
 //             end
 //           end
 //           branch_in_dec: begin
 //             // cond branch operation
 //             // All branches take two cycles in fixed time execution mode, regardless of branch
  //            // condition.
  //            // SEC_CM: CORE.DATA_REG_SW.SCA
 //             id_fsm_d         = (data_ind_timing_i || (!BranchTargetALU && branch_decision_i)) ?
 //                                    MULTI_CYCLE : FIRST_CYCLE;
 //             stall_branch     = 1;
 //             branch_set_raw_d = (branch_decision_i | data_ind_timing_i);
//
 //             if (BranchPredictor) begin
 //               branch_not_set = ~branch_decision_i;
 //             end
//
 //             perf_branch_o = 1'b1;
 //           end
 //           jump_in_dec: begin
 //             // uncond branch operation
 //             // BTALU means jumps only need one cycle
 //             //id_fsm_d      = BranchTargetALU ? FIRST_CYCLE : MULTI_CYCLE;
 //             //stall_jump    = ~BranchTargetALU;
 //             id_fsm_d      = MULTI_CYCLE;
 //             stall_jump    = 1;
 //             jump_set_raw  = jump_set_dec;
 //           end
 //           alu_multicycle_dec: begin
 //             stall_alu     = 1'b1;
 //             id_fsm_d      = MULTI_CYCLE;
 //             rf_we_raw     = 1'b0;
 //           end
 //           default: begin
 //             id_fsm_d      = FIRST_CYCLE;
 //           end
 //         endcase
 //       end

 //       MULTI_CYCLE: begin
 //         if(multdiv_en_dec) begin
 //           rf_we_raw       = rf_we_dec & ex_valid_i;
 //         end

 //         if (multicycle_done & ready_wb_i) begin
 //           id_fsm_d        = FIRST_CYCLE;
 //         end else begin
 //           stall_multdiv   = multdiv_en_dec;
 //           stall_branch    = branch_in_dec;
 //           stall_jump      = jump_in_dec;
 //         end
 //       end

 //       default: begin
 //         id_fsm_d          = FIRST_CYCLE;
 //       end
 //     endcase
 //   end
 // end

typedef enum logic [1:0] { FIRST_CYCLE, MULTI_CYCLE, SECOND_CYCLE } id_fsm_e;
  id_fsm_e id_fsm_q, id_fsm_d;

  always_ff @(posedge clk_i or negedge rst_ni) begin : id_pipeline_reg
    if (!rst_ni) begin
      id_fsm_q <= FIRST_CYCLE;
    end else if (instr_executing) begin
      id_fsm_q <= id_fsm_d;
    end
  end

  // ID/EX stage can be in two states, FIRST_CYCLE and MULTI_CYCLE. An instruction enters
  // MULTI_CYCLE if it requires multiple cycles to complete regardless of stalls and other
  // considerations. An instruction may be held in FIRST_CYCLE if it's unable to begin executing
  // (this is controlled by instr_executing).

  always_comb begin
    id_fsm_d                = id_fsm_q;
    rf_we_raw               = rf_we_dec;
    stall_multdiv           = 1'b0;
    stall_jump              = 1'b0;
    stall_branch            = 1'b0;
    stall_alu               = 1'b0;
    branch_set_raw_d        = 1'b0;
    branch_not_set          = 1'b0;
    jump_set_raw            = 1'b0;
    perf_branch_o           = 1'b0;

    if (instr_executing_spec) begin
      unique case (id_fsm_q)
        FIRST_CYCLE: begin
          unique case (1'b1)
            lsu_req_dec: begin
                if(~lsu_req_done_i) begin
                  id_fsm_d  = MULTI_CYCLE;
                end
            end
            multdiv_en_dec: begin
              // MUL or DIV operation
              if (1) begin
                // When single-cycle multiply is configured mul can finish in the first cycle so
                // only enter MULTI_CYCLE state if a result isn't immediately available
                id_fsm_d      = MULTI_CYCLE;
                rf_we_raw     = 1'b0;
                stall_multdiv = 1'b1;
              end
            end
            branch_in_dec: begin
              // cond branch operation
              // All branches take two cycles in fixed time execution mode, regardless of branch
              // condition.
              // SEC_CM: CORE.DATA_REG_SW.SCA
//              id_fsm_d         = (data_ind_timing_i || (!BranchTargetALU && branch_decision_i)) ?
//                                     MULTI_CYCLE : FIRST_CYCLE;
//              stall_branch     = (~BranchTargetALU & branch_decision_i) | data_ind_timing_i;
//              branch_set_raw_d = (branch_decision_i | data_ind_timing_i);
              
              id_fsm_d = SECOND_CYCLE ;
              stall_branch = 1;
              branch_set_raw_d = branch_decision_i;

              if (BranchPredictor) begin
                branch_not_set = ~branch_decision_i;
              end

              perf_branch_o = 1'b1;
            end
            jump_in_dec: begin
              // uncond branch operation
              // BTALU means jumps only need one cycle
//              id_fsm_d      = BranchTargetALU ? FIRST_CYCLE : MULTI_CYCLE;
//              stall_jump    = ~BranchTargetALU;
//              jump_set_raw  = jump_set_dec;
              
              id_fsm_d      = SECOND_CYCLE  ;
              stall_jump    = 1;
              jump_set_raw  = jump_set_dec;
            end
            alu_multicycle_dec: begin
              stall_alu     = 1'b1;
              id_fsm_d      = MULTI_CYCLE;
              rf_we_raw     = 1'b0;
            end
            default: begin
              id_fsm_d      = FIRST_CYCLE;
            end
          endcase
        end

        MULTI_CYCLE: begin
          if(multdiv_en_dec) begin
            rf_we_raw       = rf_we_dec & ex_valid_i;
          end
          if (multicycle_done & ready_wb_i) begin
            id_fsm_d        = FIRST_CYCLE;
          end else begin
            stall_multdiv   = multdiv_en_dec;
           // stall_branch    = branch_in_dec;
           // stall_jump      = jump_in_dec;
          end
        end
        SECOND_CYCLE: begin
            unique case (1'b1)
                branch_in_dec: begin
                   id_fsm_d = FIRST_CYCLE ;
                   stall_branch = 0;
                   branch_set_raw_d = branch_decision_i; 
                end
                jump_in_dec: begin
                   id_fsm_d = FIRST_CYCLE ;
                   stall_jump = 0;
                   jump_set_raw = jump_set_dec; 
                end
                multdiv_en_dec: begin end
                alu_multicycle_dec: begin end       
            endcase
        end
        default: begin
          id_fsm_d          = FIRST_CYCLE;
        end
      endcase
    end
  end

  assign multdiv_ready_id_o = ready_wb_i;
  // Stall ID/EX stage for reason that relates to instruction in ID/EX, update assertion below if
  // modifying this.
  assign stall_id = stall_ld_hz | stall_mem | stall_multdiv | stall_jump | stall_branch |
                      stall_alu;

  assign instr_done = ~stall_id & ~flush_id & instr_executing;

  // Signal instruction in ID is in it's first cycle. It can remain in its
  // first cycle if it is stalled.
  assign instr_first_cycle      = instr_valid_i & (id_fsm_q == FIRST_CYCLE);
  // Used by RVFI to know when to capture register read data
  // Used by ALU to access RS3 if ternary instruction.
  assign instr_first_cycle_id_o = instr_first_cycle;
  // Register read address matches write address in WB
    logic rf_rd_a_wb_match;
    logic rf_rd_b_wb_match;
    // Hazard between registers being read and written
    logic rf_rd_a_hz;
    logic rf_rd_b_hz;

    logic outstanding_memory_access;

    logic instr_kill;

    assign multicycle_done = lsu_req_dec ? ~stall_mem : ex_valid_i;

    // Is a memory access ongoing that isn't finishing this cycle
    logic outstanding_load_wb_i = 1'b0;
    logic outstanding_store_wb_i = 1'b0;
    assign outstanding_memory_access = (outstanding_load_wb_i | outstanding_store_wb_i) &
                                       ~lsu_resp_valid_i;

    // Can start a new memory access if any previous one has finished or is finishing
    assign data_req_allowed = ~outstanding_memory_access;

    // Instruction won't execute because:
    // - There is a pending exception in writeback
    //   The instruction in ID/EX will be flushed and the core will jump to an exception handler
    // - The controller isn't running instructions
    //   This either happens in preparation for a flush and jump to an exception handler e.g. in
    //   response to an IRQ or debug request or whilst the core is sleeping or resetting/fetching
    //   first instruction in which case any valid instruction in ID/EX should be ignored.
    // - There was an error on instruction fetch
    assign instr_kill = instr_fetch_err_i |
                        wb_exception      |
                        id_exception      |
                        ~controller_run;

    // With writeback stage instructions must be prevented from executing if there is:
    // - A load hazard
    // - A pending memory access
    //   If it receives an error response this results in a precise exception from WB so ID/EX
    //   instruction must not execute until error response is known).
    // - A load/store error
    //   This will cause a precise exception for the instruction in WB so ID/EX instruction must not
    //   execute
    //
    // instr_executing_spec is a speculative signal. It indicates an instruction can execute
    // assuming there are no exceptions from writeback and any outstanding memory access won't
    // receive an error. It is required so branch and jump requests don't factor in an incoming dmem
    // error (that in turn would factor directly into imem requests leading to a feedthrough path).
    //
    // instr_executing is the full signal, it will only allow execution once any potential
    // exceptions from writeback have been resolved.
    assign instr_executing_spec = instr_valid_i      &
                                  ~instr_fetch_err_i &
                                  controller_run     &
                                  ~stall_ld_hz;

    assign instr_executing = instr_valid_i              &
                             ~instr_kill                &
                             ~stall_ld_hz               &
                             ~outstanding_memory_access;

//    //`ASSERT(IbexExecutingSpecIfExecuting, instr_executing |-> instr_executing_spec)

//    //`ASSERT(IbexStallIfValidInstrNotExecuting,
//      instr_valid_i & ~instr_kill & ~instr_executing |-> stall_id)

//    //`ASSERT(IbexCannotRetireWithPendingExceptions,
//      instr_done |-> ~(wb_exception | outstanding_memory_access))

    // Stall for reasons related to memory:
    // * There is an outstanding memory access that won't resolve this cycle (need to wait to allow
    //   precise exceptions)
    // * There is a load/store request not being granted or which is unaligned and waiting to issue
    //   a second request (needs to stay in ID for the address calculation)
    assign stall_mem = instr_valid_i &
                       (outstanding_memory_access | (lsu_req_dec & ~lsu_req_done_i));

    // If we stall a load in ID for any reason, it must not make an LSU request
    // (otherwide we might issue two requests for the same instruction)
//    //`ASSERT(IbexStallMemNoRequest,
//      instr_valid_i & lsu_req_dec & ~instr_done |-> ~lsu_req_done_i)

    logic rf_ren_a = rf_ren_a_i;
    logic rf_ren_b = rf_ren_b_i;

    assign rf_rd_a_wb_match = (rf_waddr_wb_i == rf_raddr_a_i) & |rf_raddr_a_i;
    assign rf_rd_b_wb_match = (rf_waddr_wb_i == rf_raddr_b_i) & |rf_raddr_b_i;

    assign rf_rd_a_wb_match_o = rf_rd_a_wb_match;
    assign rf_rd_b_wb_match_o = rf_rd_b_wb_match;

    // If instruction is reading register that load will be writing stall in
    // ID until load is complete. No need to stall when reading zero register.
    assign rf_rd_a_hz = rf_rd_a_wb_match & rf_ren_a;
    assign rf_rd_b_hz = rf_rd_b_wb_match & rf_ren_b;

    // If instruction is read register that writeback is writing forward writeback data to read
    // data. Note this doesn't factor in load data as it arrives too late, such hazards are
    // resolved via a stall (see above).
    // forwarding data here
    // assign rf_rdata_a_fwd = rf_rd_a_wb_match & rf_write_wb_i ? rf_wdata_fwd_wb_i : rf_rdata_a_i;
    // assign rf_rdata_b_fwd = rf_rd_b_wb_match & rf_write_wb_i ? rf_wdata_fwd_wb_i : rf_rdata_b_i;
    
    // logic outstanding_load_wb_i = 1'b0;

    assign stall_ld_hz = outstanding_load_wb_i & (rf_rd_a_hz | rf_rd_b_hz);

    assign instr_type_wb_o = ~lsu_req_dec ? WB_INSTR_OTHER :
                              lsu_we      ? WB_INSTR_STORE :
                                            WB_INSTR_LOAD;

    assign instr_id_done_o = en_wb_o & ready_wb_i;

    // Stall ID/EX as instruction in ID/EX cannot proceed to writeback yet
    assign stall_wb = en_wb_o & ~ready_wb_i;

    assign perf_dside_wait_o = instr_valid_i & ~instr_kill &
                               (outstanding_memory_access | stall_ld_hz);

    // With writeback stage load/store responses are processed in the writeback stage so the ID/EX
    // stage is never expecting a load or store response.
    assign expecting_load_resp_o  = 1'b0;
    assign expecting_store_resp_o = 1'b0;

    assign instr_perf_count_id_o = ~ebrk_insn & ~ecall_insn_dec & ~illegal_insn_dec &
      ~illegal_csr_insn_i & ~instr_fetch_err_i;

  // An instruction is ready to move to the writeback stage (or retire if there is no writeback
  // stage)
  assign en_wb_o = instr_done;

  assign perf_mul_wait_o = stall_multdiv & mult_en_dec;
  assign perf_div_wait_o = stall_multdiv & div_en_dec;

endmodule
