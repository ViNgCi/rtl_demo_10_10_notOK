//`timescale 1ns / 1ps
//////////////////////////////////////////////////////////////////////////////////
// Company: 
// Engineer: 
// 
// Create Date: 09/19/2024 03:03:13 PM
// Design Name: 
// Module Name: IF_top
// Project Name: 
// Target Devices: 
// Tool Versions: 
// Description: 
// 
// Dependencies: 
// 
// Revision:
// Revision 0.01 - File Created
// Additional Comments:
// 
//////////////////////////////////////////////////////////////////////////////////


module IF_top import ibex_pkg::*; #(
  parameter int unsigned DmHaltAddr        = 32'h1A110800,
  parameter int unsigned DmExceptionAddr   = 32'h1A110808,
  parameter bit          DummyInstructions = 1'b0,
  parameter bit          ICache            = 1'b0,
  parameter bit          ICacheECC         = 1'b0,
  parameter int unsigned BusSizeECC        = BUS_SIZE,
  parameter int unsigned TagSizeECC        = IC_TAG_SIZE,
  parameter int unsigned LineSizeECC       = IC_LINE_SIZE,
  parameter bit          PCIncrCheck       = 1'b0,
  parameter bit          ResetAll          = 1'b0,
  parameter lfsr_seed_t  RndCnstLfsrSeed   = RndCnstLfsrSeedDefault,
  parameter lfsr_perm_t  RndCnstLfsrPerm   = RndCnstLfsrPermDefault,
  parameter bit          BranchPredictor   = 1'b0,
  parameter bit          MemECC            = 1'b0,
  parameter int unsigned MemDataWidth      = MemECC ? 32 + 7 : 32
)
(   
    input  logic                         clk_i,
    input  logic                         rst_ni,
    
    input  logic [31:0]                  boot_addr_i,              // also used for mtvec
    input  logic                         req_i,                    // instruction request control

    // instruction cache interface
     output logic                        instr_req_o,
     output logic [31:0]                 instr_addr_o,
     input  logic                        instr_gnt_i,
     input  logic                        instr_rvalid_i,
     input  logic [MemDataWidth-1:0]     instr_rdata_i,
     input  logic                        instr_bus_err_i,
     output logic                        instr_intg_err_o,
     
    // ICache RAM IO
      output logic [IC_NUM_WAYS-1:0]      ic_tag_req_o,
      output logic                        ic_tag_write_o,
      output logic [IC_INDEX_W-1:0]       ic_tag_addr_o,
      output logic [TagSizeECC-1:0]       ic_tag_wdata_o,
      input  logic [TagSizeECC-1:0]       ic_tag_rdata_i [IC_NUM_WAYS],
      output logic [IC_NUM_WAYS-1:0]      ic_data_req_o,
      output logic                        ic_data_write_o,
      output logic [IC_INDEX_W-1:0]       ic_data_addr_o,
      output logic [LineSizeECC-1:0]      ic_data_wdata_o,
      input  logic [LineSizeECC-1:0]      ic_data_rdata_i [IC_NUM_WAYS],
      input  logic                        ic_scr_key_valid_i,
      output logic                        ic_scr_key_req_o,
      
      // control signals
      input  logic                        instr_valid_clear_i,      // clear instr valid bit in IF-ID
      input  logic                        pc_set_i,                 // set the PC to a new value
      input  pc_sel_e                     pc_mux_i,                 // selector for PC multiplexer
      input  logic                        nt_branch_mispredict_i,   // Not-taken branch in ID/EX was
                                                                    // mispredicted (predicted taken)
      input  logic [31:0]                 nt_branch_addr_i,         // Not-taken branch address in ID/EX
      input  exc_pc_sel_e                 exc_pc_mux_i,             // selects ISR address
      input  exc_cause_t                  exc_cause,                // selects ISR address for
                                                                    // vectorized interrupt lines
      input  logic                        dummy_instr_en_i,
      input  logic [2:0]                  dummy_instr_mask_i,
      input  logic                        dummy_instr_seed_en_i,
      input  logic [31:0]                 dummy_instr_seed_i,
      input  logic                        icache_enable_i,
      input  logic                        icache_inval_i,
      output logic                        icache_ecc_error_o,
      
      // jump and branch target
      input  logic [31:0]                 branch_target_ex_i,       // branch/jump target address
    
      // CSRs
      input  logic [31:0]                 csr_mepc_i,               // PC to restore after handling
                                                                    // the interrupt/exception
      input  logic [31:0]                 csr_depc_i,               // PC to restore after handling
                                                                    // the debug request
      input  logic [31:0]                 csr_mtvec_i,              // base PC to jump to on exception
      output logic                        csr_mtvec_init_o,         // tell CS regfile to init mtvec
    
      // pipeline stall
      input  logic                        id_in_ready_i,            // ID stage is ready for new instr
    
      // misc signals
      output logic                        pc_mismatch_alert_o,
      output logic                        if_busy_o,                 // IF stage is busy fetching instr
      
      // output of ID stage
      output logic                        instr_valid_id_o,         // instr in IF-ID is valid
      output logic                        instr_new_id_o,           // instr in IF-ID is new
      output logic [31:0]                 instr_rdata_id_o,         // instr for ID stage
      output logic [31:0]                 instr_rdata_alu_id_o,     // replicated instr for ID stage
                                                                    // to reduce fan-out
      output logic [15:0]                 instr_rdata_c_id_o,       // compressed instr for ID stage
                                                                    // (mtval), meaningful only if
                                                                    // instr_is_compressed_id_o = 1'b1
      output logic                        instr_is_compressed_id_o, // compressed decoder thinks this
                                                                    // is a compressed instr
      output logic                        instr_bp_taken_o,         // instruction was predicted to be
                                                                    // a taken branch
      output logic                        instr_fetch_err_o,        // bus error on fetch
      output logic                        instr_fetch_err_plus2_o,  // bus error misaligned
      output logic                        illegal_c_insn_id_o,      // compressed decoder thinks this
                                                                    // is an invalid instr
      output logic                        dummy_instr_id_o,         // Instruction is a dummy
      output logic [31:0]                 pc_if_o,
      output logic [31:0]                 pc_id_o,
      input  logic                        pmp_err_if_i,
      input  logic                        pmp_err_if_plus2_i
     
      
    );
      logic              instr_valid_id_d, instr_valid_id_q;
      logic              instr_new_id_d, instr_new_id_q;
    
      logic              instr_err, instr_intg_err;
    
      // prefetch buffer related signals
      logic              prefetch_busy;
      logic              branch_req;
      logic       [31:0] fetch_addr_n;
      logic              unused_fetch_addr_n0;
    
      logic              prefetch_branch;
      logic [31:0]       prefetch_addr;
    
      logic              fetch_valid_raw;
      logic              fetch_valid;
      logic              fetch_ready;
      logic       [31:0] fetch_rdata;
      logic       [31:0] fetch_addr;
      logic              fetch_err;
      logic              fetch_err_plus2;
    
      logic [31:0]       instr_decompressed;
      logic              illegal_c_insn;
      logic              instr_is_compressed;
    
      logic              if_instr_valid;
      logic       [31:0] if_instr_rdata;
      logic       [31:0] if_instr_addr;
      logic              if_instr_bus_err;
      logic              if_instr_pmp_err;
      logic              if_instr_err;
      logic              if_instr_err_plus2;
    
      logic       [31:0] exc_pc;
    
      logic              if_id_pipe_reg_we; // IF-ID pipeline reg write enable
    
      // Dummy instruction signals
      logic              stall_dummy_instr;
      logic [31:0]       instr_out;
      logic              instr_is_compressed_out;
      logic              illegal_c_instr_out;
      logic              instr_err_out;
    
      logic              predict_branch_taken;
      logic       [31:0] predict_branch_pc;
    
      logic        [4:0] irq_vec;
 ////////////////////////////////////////////////////////////////////////////////
 
     //////////
     // PC   //
     /////////     
    PC #(
     .DmHaltAddr         (32'h1A110800),
     .DmExceptionAddr    (32'h1A110808)
     ) pc(
     .boot_addr_i(boot_addr_i),
    
    // Input control signal
    .pc_set_i(pc_set_i),                 // set the PC to a new value
    .pc_mux_i(pc_mux_i),                 // selector for PC multiplexer

    .exc_pc_mux_i(exc_pc_mux_i),             // selects ISR address
    .exc_cause(exc_cause),                // selects ISR address for
                                 // vectorized interrupt lines
    // Branch input
    .predict_branch_pc(predict_branch_pc),
    .predict_branch_taken(predict_branch_taken),
    .branch_target_ex_i(branch_target_ex_i),       // branch/jump target address
    
    
    // CSRs input 
    .csr_mepc_i(csr_mepc_i),               // PC to restore after handling
                                                                    // the interrupt/exception
    .csr_depc_i(csr_depc_i),               // PC to restore after handling
                                                                    // the debug request
    .csr_mtvec_i(csr_mtvec_i),              // base PC to jump to on exception
    
    // Addr
    .fetch_addr_n(fetch_addr_n),
    .csr_mtvec_init_o(csr_mtvec_init_o)         // tell CS regfile to init mtvec
     );     
    //   SEC_CM: BUS.INTEGRITY
    assign instr_intg_err            = 1'b0;        // NO MEMECC
    assign instr_err        = instr_intg_err | instr_bus_err_i;
    assign instr_intg_err_o = instr_intg_err & instr_rvalid_i;
    
    // BRANCH
    
    // There are two possible "branch please" signals that are computed in the IF stage: branch_req
  // and nt_branch_mispredict_i. These should be mutually exclusive (see the NoMispredBranch
  // assertion), so we can just OR the signals together.
     assign prefetch_branch = branch_req | nt_branch_mispredict_i;
     assign prefetch_addr   = branch_req ? {fetch_addr_n[31:1], 1'b0} : nt_branch_addr_i;

  // The fetch_valid signal that comes out of the icache or prefetch buffer should be squashed if we
  // had a misprediction.
     assign fetch_valid = fetch_valid_raw & ~nt_branch_mispredict_i;

  // We should never see a mispredict and an incoming branch on the same cycle. The mispredict also
  // cancels any predicted branch so overall branch_req must be low.
 // //`ASSERT(NoMispredBranch, nt_branch_mispredict_i |-> ~branch_req)
 
     ///////////
    // ICache //
    ///////////
    
    /*ibex_icache #(
      .ICacheECC       (ICacheECC),
      .ResetAll        (ResetAll),
      .BusSizeECC      (BusSizeECC),
      .TagSizeECC      (TagSizeECC),
      .LineSizeECC     (LineSizeECC)
    ) icache_i (
        .clk_i               ( clk_i                      ),
        .rst_ni              ( rst_ni                     ),

        .req_i               ( req_i                      ),

        .branch_i            ( prefetch_branch            ),        //
        .addr_i              ( prefetch_addr              ),        //

        .ready_i             ( fetch_ready                ),        //
        .valid_o             ( fetch_valid_raw            ),        
        .rdata_o             ( fetch_rdata                ),        
        .addr_o              ( fetch_addr                 ),        
        .err_o               ( fetch_err                  ),        
        .err_plus2_o         ( fetch_err_plus2            ),        

        .instr_req_o         ( instr_req_o                ),
        .instr_addr_o        ( instr_addr_o               ),
        .instr_gnt_i         ( instr_gnt_i                ),
        .instr_rvalid_i      ( instr_rvalid_i             ),
        .instr_rdata_i       ( instr_rdata_i[31:0]        ),
        .instr_err_i         ( instr_err                  ),        //

        .ic_tag_req_o        ( ic_tag_req_o               ),
        .ic_tag_write_o      ( ic_tag_write_o             ),
        .ic_tag_addr_o       ( ic_tag_addr_o              ),
        .ic_tag_wdata_o      ( ic_tag_wdata_o             ),
        .ic_tag_rdata_i      ( ic_tag_rdata_i             ),
        .ic_data_req_o       ( ic_data_req_o              ),
        .ic_data_write_o     ( ic_data_write_o            ),
        .ic_data_addr_o      ( ic_data_addr_o             ),
        .ic_data_wdata_o     ( ic_data_wdata_o            ),
        .ic_data_rdata_i     ( ic_data_rdata_i            ),
        .ic_scr_key_valid_i  ( ic_scr_key_valid_i         ),
        .ic_scr_key_req_o    ( ic_scr_key_req_o           ),

        .icache_enable_i     ( icache_enable_i            ),
        .icache_inval_i      ( icache_inval_i             ),
        .busy_o              ( prefetch_busy              ),        //
        .ecc_error_o         ( icache_ecc_error_o         )
    );*/

    ibex_prefetch_buffer #(
	.ResetAll	(ResetAll)
    ) prefetch_buffer_i (
	.clk_i	(clk_i),
	.rst_ni (rst_ni),
	.req_i	(req_i),
	.branch_i	(prefetch_branch),
	.addr_i		(prefetch_addr),
	.ready_i	(fetch_ready),
	.valid_o	(fetch_valid_raw),
	.rdata_o	(fetch_rdata),
	.addr_o		(fetch_addr),
	.err_o               ( fetch_err                  ),
	.err_plus2_o         ( fetch_err_plus2            ),
	.instr_req_o         ( instr_req_o                ),
	.instr_addr_o        ( instr_addr_o               ),
    	.instr_gnt_i         ( instr_gnt_i                ),
	.instr_rvalid_i      ( instr_rvalid_i             ),
	.instr_rdata_i       ( instr_rdata_i[31:0]        ),
	.instr_err_i         ( instr_err                  ),
	.busy_o              ( prefetch_busy              )
    );
    assign unused_fetch_addr_n0 = fetch_addr_n[0];
    assign branch_req  = pc_set_i | predict_branch_taken;
    assign pc_if_o     = if_instr_addr;
    assign if_busy_o   = prefetch_busy;
/////////////////////////////////////////////////////////////////////////

////////////////////
//FSM & Controller//
////////////////////


////////////////////
//   PMP errors  //
////////////////////

//   An error can come from the instruction address, or the next instruction address for unaligned,
//   uncompressed instructions.
  assign if_instr_pmp_err = pmp_err_if_i |
                            (if_instr_addr[1] & ~instr_is_compressed & pmp_err_if_plus2_i);

  // Combine bus errors and pmp errors
  assign if_instr_err = if_instr_bus_err | if_instr_pmp_err;

  // Capture the second half of the address for errors on the second part of an instruction
  assign if_instr_err_plus2 = ((if_instr_addr[1] & ~instr_is_compressed & pmp_err_if_plus2_i) |
                               fetch_err_plus2) & ~pmp_err_if_i;

//   compressed instruction decoding, or more precisely compressed instruction
//   expander
  
//   since it does not matter where we decompress instructions, we do it here
//   to ease timing closure 

    ///////////////////
    // Comp_decoder //
    ///////////////////
    
    ibex_compressed_decoder compressed_decoder_i (
    .clk_i          (clk_i),
    .rst_ni         (rst_ni),
    .valid_i        (fetch_valid & ~fetch_err),                     //
    .instr_i        (if_instr_rdata),                               //
    .instr_o        (instr_decompressed),
    .is_compressed_o(instr_is_compressed),
    .illegal_instr_o(illegal_c_insn)
  );
  
  
  // NO DUMMY INSTRUCTIONS 
  // GEN_NO_DUMMY_INSTRUCTION : begin
    logic        unused_dummy_en;
    logic [2:0]  unused_dummy_mask;
    logic        unused_dummy_seed_en;
    logic [31:0] unused_dummy_seed;

    assign unused_dummy_en         = dummy_instr_en_i;
    assign unused_dummy_mask       = dummy_instr_mask_i;
    assign unused_dummy_seed_en    = dummy_instr_seed_en_i;
    assign unused_dummy_seed       = dummy_instr_seed_i;
    
    assign instr_out               = instr_decompressed;
    assign instr_is_compressed_out = instr_is_compressed;
    assign illegal_c_instr_out     = illegal_c_insn;
    assign instr_err_out           = if_instr_err;
    assign stall_dummy_instr       = 1'b0;
    assign dummy_instr_id_o        = 1'b0;
// end
    // NO BRANCH PREDICTION
    // GEN_NO_BRANCH_PREDICTION : begin
    assign instr_bp_taken_o     = 1'b0;
    assign predict_branch_taken = 1'b0;
    assign predict_branch_pc    = 32'b0;

    assign if_instr_valid = fetch_valid;
    assign if_instr_rdata = fetch_rdata;
    assign if_instr_addr  = fetch_addr;
    assign if_instr_bus_err = fetch_err;
    assign fetch_ready = id_in_ready_i & ~stall_dummy_instr;
  // end
/////////////////////////////////////////////////////////////////////

    //////////////////////////
    //    ID/IF Register    //
    //////////////////////////
    
    
  // The ID stage becomes valid as soon as any instruction is registered in the ID stage flops.
  // Note that the current instruction is squashed by the incoming pc_set_i signal.
  // Valid is held until it is explicitly cleared (due to an instruction completing or an exception)
  assign instr_valid_id_d = (if_instr_valid & id_in_ready_i & ~pc_set_i) |
                            (instr_valid_id_q & ~instr_valid_clear_i);
  assign instr_new_id_d   = if_instr_valid & id_in_ready_i;

  always_ff @(posedge clk_i or negedge rst_ni) begin
    if (!rst_ni) begin
      instr_valid_id_q <= 1'b0;
      instr_new_id_q   <= 1'b0;
    end else begin
      instr_valid_id_q <= instr_valid_id_d;
      instr_new_id_q   <= instr_new_id_d;
    end
  end

  assign instr_valid_id_o = instr_valid_id_q;
  // Signal when a new instruction enters the ID stage (only used for RVFI signalling).
  assign instr_new_id_o   = instr_new_id_q;

  // IF-ID pipeline registers, frozen when the ID stage is stalled
  assign if_id_pipe_reg_we = instr_new_id_d;

  if (ResetAll) begin : g_instr_rdata_ra
    always_ff @(posedge clk_i or negedge rst_ni) begin
      if (!rst_ni) begin
        instr_rdata_id_o         <= '0;
        instr_rdata_alu_id_o     <= '0;
        instr_fetch_err_o        <= '0;
        instr_fetch_err_plus2_o  <= '0;
        instr_rdata_c_id_o       <= '0;
        instr_is_compressed_id_o <= '0;
        illegal_c_insn_id_o      <= '0;
        pc_id_o                  <= '0;
      end else if (if_id_pipe_reg_we) begin
        instr_rdata_id_o         <= instr_out;
        // To reduce fan-out and help timing from the instr_rdata_id flops they are replicated.
        instr_rdata_alu_id_o     <= instr_out;
        instr_fetch_err_o        <= instr_err_out;
        instr_fetch_err_plus2_o  <= if_instr_err_plus2;
        instr_rdata_c_id_o       <= if_instr_rdata[15:0];
        instr_is_compressed_id_o <= instr_is_compressed_out;
        illegal_c_insn_id_o      <= illegal_c_instr_out;
        pc_id_o                  <= pc_if_o;
      end
    end
  end else begin : g_instr_rdata_nr
    always_ff @(posedge clk_i) begin
      if (if_id_pipe_reg_we) begin
        instr_rdata_id_o         <= instr_out;
        // To reduce fan-out and help timing from the instr_rdata_id flops they are replicated.
        instr_rdata_alu_id_o     <= instr_out;
        instr_fetch_err_o        <= instr_err_out;
        instr_fetch_err_plus2_o  <= if_instr_err_plus2;
        instr_rdata_c_id_o       <= if_instr_rdata[15:0];
        instr_is_compressed_id_o <= instr_is_compressed_out;
        illegal_c_insn_id_o      <= illegal_c_instr_out;
        pc_id_o                  <= pc_if_o;
      end
    end
  end
  
  assign pc_mismatch_alert_o = 1'b0;        // NO INCRE PC CHECK
////////////////////////////////////////////////////////////////////////////
endmodule
