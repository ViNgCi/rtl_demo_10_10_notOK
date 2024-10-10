//`timescale 1ns / 1ps
//////////////////////////////////////////////////////////////////////////////////
// Company: 
// Engineer: 
// 
// Create Date: 09/19/2024 09:03:25 PM
// Design Name: 
// Module Name: ID_top
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


module ID_top import ibex_pkg::*; #(
  parameter bit               RV32E           = 0,
  parameter ibex_pkg::rv32m_e RV32M           = ibex_pkg::RV32MFast,
  parameter ibex_pkg::rv32b_e RV32B           = ibex_pkg::RV32BBalanced,
  parameter bit               DataIndTiming   = 1'b0,
  parameter bit               BranchTargetALU = 1,
  parameter bit               WritebackStage  = 0,
  parameter bit               BranchPredictor = 0,
  parameter bit               MemECC          = 1'b0
)
(
  input  logic                      clk_i,
  input  logic                      rst_ni,
  
  // Interface to IF stage
  input  logic                      instr_valid_i,
  input  logic                      instr_fetch_err_i,
  input  logic [31:0]               instr_rdata_i,         // from IF-ID pipeline registers
  input  logic [31:0]               instr_rdata_alu_i,     // from IF-ID pipeline registers
  input  logic                      instr_is_compressed_i,
  input  logic                      illegal_c_insn_i,
  input  logic [31:0]               pc_id_i,                    // ==> pipeline
 
  
  //input  logic                      branch_decision_i,
  // Branch
  input logic                       instr_first_cycle_i,        // FROM FSM
  input logic                       branch_taken_i,             // FROM FSM
  
  // LSU INTERFACE
  output logic                      lsu_req_EX,
  output logic                      lsu_we_EX,
  output logic [1:0]                lsu_type_EX,
  output logic                      lsu_sign_ext_EX,
  output logic [31:0]               lsu_wdata_EX,

  // MUL, DIV INTERFACE
  output logic                      mult_en_EX,           // ==> PIPELINE
  output logic                      div_en_EX,            // ==> PIPELINE
  output logic                      mult_sel_EX,          // ==> PIPELINE
  output logic                      div_sel_EX,           // ==> PIPELINE
  output ibex_pkg::md_op_e          multdiv_operator_EX,  // ==> PIPELINE
  output logic  [1:0]               multdiv_signed_mode_EX,// ==> PIPELINE
  
  // CSR
  output logic                      csr_access_EX,
  output ibex_pkg::csr_op_e         csr_op_EX,
  output logic                      csr_op_en_EX,
  
  // REG_FILE 
  // READ
  output logic [4:0]                rf_raddr_a_o,            
  input  logic [31:0]               rf_rdata_a_i,           
  output logic [4:0]                rf_raddr_b_o,
  input  logic [31:0]               rf_rdata_b_i,
  output logic                      rf_ren_a_o,
  output logic                      rf_ren_b_o,           
  
  output  logic [31:0]              rf_rdata_a_EX, // ==> PIPELINE
  output  logic [31:0]              rf_rdata_b_EX, // ==> PIPELINE
  
  // WRITE
  output ibex_pkg::rf_wd_sel_e      rf_wdata_sel_EX,   // RF write data selection
  output logic                      rf_we_EX,          // write enable for regfile
  output logic [4:0]                rf_waddr_EX,
  
  // IMM
  output imm_a_sel_e                imm_a_mux_sel_EX,
  output imm_b_sel_e                imm_b_mux_sel_EX,
  
  output [31:0] instr_EX,
  output [4:0] instr_rs1_EX,
  output [4:0] instr_rs2_EX,
  output [4:0] instr_rs3_EX,
  output [4:0] instr_rd_EX,
  output [31:0] pc_EX,
  output logic instr_is_compressed_EX,
     
  output [31:0] imm_i_type_EX,
  output [31:0] imm_b_type_EX,
  output [31:0] imm_s_type_EX,
  output [31:0] imm_j_type_EX,
  output [31:0] imm_u_type_EX,
  output [31:0] zimm_rs1_type_EX,
  
  // BTALU
  output op_a_sel_e                 bt_a_mux_sel_EX,
  output imm_b_sel_e                bt_b_mux_sel_EX,
     
  // ALU
  output   alu_op_e                 alu_operator_EX,
  output   op_a_sel_e               alu_op_a_mux_sel_EX,
  output   op_b_sel_e               alu_op_b_mux_sel_EX,

  //to controller
  output logic mult_en_dec,
  output logic div_en_dec,
  output logic lsu_we_dec,
  output logic lsu_req_dec,
  output logic rf_we_dec,
  output logic branch_in_dec_o,
  output logic jump_in_dec_o,

  //output logic rf_ren_a_o,
  //output logic rf_ren_b_o,

  //output logic [4:0] rf_waddr_wb_o,


  
  // CONTROLLER INTERFACE
  output logic                 illegal_insn_o,
  output logic                 ebrk_insn_o,   
  output logic                 mret_insn_o,   
                                            
  output logic                 dret_insn_o,   
  output logic                 ecall_insn_o,  
  output logic                 wfi_insn_o,    
  output logic                 jump_set_o,    
  output logic                 icache_inval_o,

  output  ibex_pkg::wb_instr_type_e instr_type_wb_o,                // =========> DAY VINH OI 
  output  logic                     instr_perf_count_id_o           // =========> DAY VINH OI 

    );
   // ID/EX Pipeline Register 
   
     // IMM
     logic [31:0] instr_ID_r;
     logic [4:0] instr_rs1_ID_r;
     logic [4:0] instr_rs2_ID_r;
     logic [4:0] instr_rs3_ID_r;
     logic [4:0] instr_rd_ID_r;
     logic [31:0] pc_ID_r;
     logic instr_is_compressed_r;
     
     logic [31:0] imm_i_type_ID_r;
     logic [31:0] imm_b_type_ID_r;
     logic [31:0] imm_s_type_ID_r;
     logic [31:0] imm_j_type_ID_r;
     logic [31:0] imm_u_type_ID_r;
     logic [31:0] zimm_rs1_type_ID_r;
     
     imm_a_sel_e    imm_a_mux_sel_dec_r;
     imm_b_sel_e    imm_b_mux_sel_dec_r;
     
     // ALU
     alu_op_e       alu_operator_ID_r;
     op_a_sel_e     alu_op_a_mux_sel_dec_r;
     op_b_sel_e     alu_op_b_mux_sel_dec_r;
     
     // BTALU
     op_a_sel_e     bt_a_mux_sel_dec_r;
     imm_b_sel_e    bt_b_mux_sel_dec_r;
     
     // MUL/DIV
     logic          mult_en_ID_r;           // ==> PIPELINE
     logic          div_en_ID_r;           // ==> PIPELINE
     logic          mult_sel_dec_r;
     logic          div_sel_dec_r;
     md_op_e        multdiv_operator_ID_r;
     logic [1:0]    multdiv_signed_mode_ID_r;
     
     // REGFILE
     rf_wd_sel_e    rf_wdata_sel_ID_r;
     logic          rf_we_ID_r;          // write enable for regfile
     logic [4:0]    rf_waddr_ID_r;
     logic          rf_ren_a_r;
     logic          rf_ren_b_r;           
     logic [31:0]   rf_rdata_a_ID_r; 
     logic [31:0]   rf_rdata_b_ID_r;

     
     
     // CSR
     logic          csr_access_ID_r;
     csr_op_e       csr_op_ID_r;
     logic          csr_op_en_ID_r;
    
    // LSU 
     logic          lsu_req_ID_r;
     logic          lsu_we_ID_r;
     logic [1:0]    lsu_type_ID_r;
     logic          lsu_sign_ext_ID_r;
     logic [31:0]   lsu_wdata_ID_r;
     
     
   //
     logic [31:0] instr;
     logic [4:0] instr_rs1;
     logic [4:0] instr_rs2; 
     logic [4:0] instr_rs3; 
     logic [4:0] instr_rd;
     
     assign instr     = instr_rdata_i;
     assign instr_rs1 = instr[19:15];
     assign instr_rs2 = instr[24:20];
     assign instr_rs3 = instr[31:27];
     assign instr_rd  = instr[11:7];
     
    // ALU Control 
     alu_op_e alu_operator_dec;
     logic alu_multicycle_dec;
     
     op_a_sel_e alu_op_a_mux_sel_dec; 
     op_b_sel_e alu_op_b_mux_sel_dec;
     
     imm_a_sel_e imm_a_mux_sel_dec;
     imm_b_sel_e imm_b_mux_sel_dec;
     
     op_a_sel_e bt_a_mux_sel_dec;
     imm_b_sel_e bt_b_mux_sel_dec;
     
     logic mult_sel_dec;
     logic div_sel_dec;
     logic use_rs3_q;

          // WB
     wb_instr_type_e           instr_type_wb;                               // =========> DAY VINH OI
     logic                     instr_perf_count_id;                         // =========> DAY VINH OI
     wb_instr_type_e           instr_type_wb_r;                             // =========> DAY VINH OI
     logic                     instr_perf_count_id_r;                       // =========> DAY VINH OI
     
    /////////////
    // IMM_GEN //
    /////////////
    logic [31:0] imm_i_type_id_o;
    logic [31:0] imm_b_type_id_o;
    logic [31:0] imm_s_type_id_o;
    logic [31:0] imm_j_type_id_o;
    logic [31:0] imm_u_type_id_o;
    logic [31:0] zimm_rs1_type_id_o;
    Imm_Gen u_imm_gen (
    .instr_rdata_i(instr_rdata_i),
    .imm_i_type_o(imm_i_type_id_o),             // ===> PIPELINE
    .imm_b_type_o(imm_b_type_id_o),             // ===> PIPELINE
    .imm_s_type_o(imm_s_type_id_o),             // ===> PIPELINE
    .imm_j_type_o(imm_j_type_id_o),             // ===> PIPELINE
    .imm_u_type_o(imm_u_type_id_o),             // ===> PIPELINE
    .zimm_rs1_type_o(zimm_rs1_type_id_o)        // ===> PIPELINE
    );
    
     //////////////////
     // ALU_DECODER //   
     ////////////////  
     alu_decoder #(
     .RV32E (0),
     .RV32M (RV32MFast),
     .RV32B (RV32B),
     .BranchTargetALU(1)
    ) u_alu_decoder
    (   
      .clk_i(clk_i),
      .rst_ni(rst_ni),
      
      .instr_first_cycle_i(instr_first_cycle_i),
      .instr_rdata_alu_i(instr_rdata_alu_i), 
      .branch_taken_i(branch_taken_i),
      
                        
        // ALU ==> pipeline
      .alu_operator_o(alu_operator_dec),        // ALU operation selection                  // ===> PIPELINE
      .alu_multicycle_o(alu_multicycle_dec),      // instr can nhieu cycle de thuc hien     // ===> FSM
      
       // ALU Operand SEL
      .alu_op_a_mux_sel_o(alu_op_a_mux_sel_dec),    // operand a selection: reg value, PC,  // ===> PIPELINE
                                                          // immediate or zero
      .alu_op_b_mux_sel_o(alu_op_b_mux_sel_dec),    // operand b selection: reg value or    // ==>  PIPELINE
                                                          // immediate                                                      
     
      // immediates sel for operand a and b
      .imm_a_mux_sel_o(imm_a_mux_sel_dec),       // immediate selection for operand a       // ==> PIPELINE
      .imm_b_mux_sel_o(imm_b_mux_sel_dec),       // immediate selection for operand b       // ==> PIPELINE
      
      .bt_a_mux_sel_o(bt_a_mux_sel_dec),        // branch target selection operand a        // ==> PIPELINE
      .bt_b_mux_sel_o(bt_b_mux_sel_dec),        // branch target selection operand b        // ==> PIPELINE
      
      // MULT/DIV Sel ==> pipeline
      .mult_sel_o(mult_sel_dec),            // as above but static, for data muxes          // ==> PIPELINE
      .div_sel_o(div_sel_dec),             // as above but static, for data muxes           // ==> PIPELINE
      
      .use_rs3_q(use_rs3_q)                                                                 // REGFILE
    ); 
    
    ////////////////////
    // INSTR_DECODER //
    ///////////////////
    md_op_e multdiv_operator_dec;
    logic [1:0] multdiv_signed_mode_dec;
    rf_wd_sel_e rf_wdata_sel;
    logic csr_access_dec;
    csr_op_e csr_op_dec;
    logic data_req_dec;
    logic data_we_dec;
    logic [1:0] data_type_dec;
    logic data_sign_extension_dec;
    logic jump_in_dec;
    logic branch_in_dec;
    assign branch_in_dec_o = branch_in_dec;
    assign jump_in_dec_o = jump_in_dec;  
    logic illegal_insn_dec;
    logic rf_we;
    logic rf_ren_a_dec;
    logic rf_ren_b_dec;
    logic jump_set_dec;
    instr_decoder #(
     .RV32E (0),
     .RV32M (RV32MFast),
     .RV32B (RV32B),
     .BranchTargetALU(1)
    ) u_instr_decoder (
      .clk_i(clk_i),
      .rst_ni(rst_ni),
        
        // from IF-ID pipeline register
      .instr_first_cycle_i(instr_first_cycle_i),   // instruction read is in its first cycle
      .instr_rdata_i(instr_rdata_i),         // instruction read from memory/cache
      .illegal_c_insn_i(illegal_c_insn_i),      // compressed instruction decode failed
    
      //  CONTROLLER INTERFACE
      .illegal_insn_o(illegal_insn_dec),        // illegal instr encountered
      
      .ebrk_insn_o(ebrk_insn_o),           // trap instr encountered
      .mret_insn_o(mret_insn_o),           // return from exception instrencountered
      .dret_insn_o(dret_insn_o),           // return from debug instr encountered
      .ecall_insn_o(ecall_insn_o),          // syscall instr encountered
      .wfi_insn_o(wfi_insn_o),            // wait for interrupt instr encountered
      
      .jump_set_o(jump_set_dec),            // jump taken set signal          // ==> FSM
      .icache_inval_o(icache_inval_o),
      
      // REG_FILE INTERFACE
      .rf_wdata_sel_o(rf_wdata_sel),   // RF write data selection             //  ==> PIPELINE FOR REGFILE DATA SELECT
      
      .rf_ren_a_o(rf_ren_a_dec),          // Instruction reads from RF addr A    // ==> REGFILE 
      .rf_ren_b_o(rf_ren_b_dec),          // Instruction reads from RF addr B    // ==> REGFILE
      
      // MULTDIV
      .multdiv_operator_o(multdiv_operator_dec),          // INSTR_DECODER        // ==> PIPELINE
      .multdiv_signed_mode_o(multdiv_signed_mode_dec),       // INSTR_DECODER     // ==> PIPELINE
      
      // CSRs
      .csr_access_o(csr_access_dec),          // access to CSR                    // ==> PIPELINE
      .csr_op_o(csr_op_dec),                 // operation to perform on CSR       // ==> PIPELINE
    
      // LSU
      .data_req_o(data_req_dec),            // start transaction to data memory   // ==> 
      .data_we_o(data_we_dec),             // write enable                        // ==> PIPELINE
      .data_type_o(data_type_dec),           // size of transaction: byte, half   // ==> 
                                                          // word or word
      .data_sign_extension_o(data_sign_extension_dec), // sign extension for data read from   // ==> 
                                                          // memory
        
      // jump/branches
      .jump_in_dec_o(jump_in_dec),         // jump is being calculated in ALU              // ==> FSM               
      .branch_in_dec_o(branch_in_dec),                                                       // ==> FSM
      .rf_we(rf_we)                                                            // ==> FSM
    );
 /////////////////////////////////////////////////////////////////////////////////////////////   
// do not enable multdiv in case of illegal instruction exception
  logic mult_en;
  logic div_en;
  logic csr_op_en;
  assign mult_en = illegal_insn_dec ? 1'b0 : mult_sel_dec;                        
  assign div_en  = illegal_insn_dec ? 1'b0 : div_sel_dec;
  
  ////////////////
  assign csr_op_en = csr_access_dec;
  ////////////
     logic          lsu_req;
     logic          lsu_we;
     logic [1:0]    lsu_type;
     logic          lsu_sign_ext;
     logic [31:0]   lsu_wdata;
     assign lsu_req = data_req_dec;         // NOT DONE YET
     assign lsu_we = data_we_dec;
     assign lsu_type = data_type_dec;
     assign lsu_sign_ext = data_sign_extension_dec;
     assign lsu_wdata = rf_rdata_b_i; // NOT DONE YET
      
     
     
 /////////////////////////////////////////////////////////////////////////////////////// 
    /////////////////////
    // ID/EX PIPELINE //
    ////////////////////
    
    always @(posedge clk_i or negedge rst_ni) begin
        if(rst_ni == 1'b0) begin 
         // IMM
         instr_ID_r <= 32'b0;
         instr_rs1_ID_r <= 5'b0;
         instr_rs2_ID_r <= 5'b0;
         instr_rs3_ID_r <= 5'b0;
         instr_rd_ID_r <= 5'b0;
         pc_ID_r <= 32'b0;
         instr_is_compressed_r <= 1'b0;
         
         imm_i_type_ID_r <= 32'b0;
         imm_b_type_ID_r <= 32'b0;
         imm_s_type_ID_r <= 32'b0;
         imm_j_type_ID_r <= 32'b0;
         imm_u_type_ID_r <= 32'b0;
         zimm_rs1_type_ID_r <= 32'b0;
         
         imm_a_mux_sel_dec_r <= IMM_A_Z;
         imm_b_mux_sel_dec_r <= IMM_B_I;
         
         // ALU
         alu_operator_ID_r <= ALU_SLTU;
         alu_op_a_mux_sel_dec_r <= OP_A_REG_A;
         alu_op_b_mux_sel_dec_r <= OP_B_REG_B;
         
         // BTALU
         bt_a_mux_sel_dec_r <= OP_A_REG_A;
         bt_b_mux_sel_dec_r <= IMM_B_I;
         
         // MUL/DIV
         mult_en_ID_r <= 1'b0;           // ==> PIPELINE
         div_en_ID_r <= 1'b0;           // ==> PIPELINE
         mult_sel_dec_r <= 1'b0;
         div_sel_dec_r <= 1'b0;
         multdiv_operator_ID_r <= MD_OP_MULL;
         multdiv_signed_mode_ID_r <= 2'b0;
         
         // REGFILE
         rf_wdata_sel_ID_r <= RF_WD_EX;
         rf_we_ID_r <= 1'b0;          // write enable for regfile
         rf_waddr_ID_r <= 5'b0;
//         rf_ren_a_r <= 1'b0;
//         rf_ren_b_r <= 1'b0;           
         rf_rdata_a_ID_r <= 32'b0; 
         rf_rdata_b_ID_r <= 32'b0; 
         
         // CSR
         csr_access_ID_r <= 1'b0;
         csr_op_ID_r <= CSR_OP_READ;
         csr_op_en_ID_r <= 1'b0;
        
        // LSU 
         lsu_req_ID_r <= 1'b0;
         lsu_we_ID_r <= 1'b0;
         lsu_type_ID_r <= 2'b0;
         lsu_sign_ext_ID_r <= 1'b0;
         lsu_wdata_ID_r <= 32'b0; 

         instr_perf_count_id_r <= 1'b0;                         // =========> DAY VINH OI
         instr_type_wb_r <= wb_instr_type_e'(0);                // =========> DAY VINH OI

        end else 
        begin
        // IMM
         instr_ID_r <= instr_rdata_i;
         instr_rs1_ID_r <= instr_rs1;
         instr_rs2_ID_r <= instr_rs2;
         instr_rs3_ID_r <= instr_rs3;
         instr_rd_ID_r  <= instr_rd;
         pc_ID_r <= pc_id_i;
         instr_is_compressed_r <= instr_is_compressed_i;
         
         imm_i_type_ID_r <= imm_i_type_id_o;
         imm_b_type_ID_r <= imm_b_type_id_o;
         imm_s_type_ID_r <= imm_s_type_id_o;
         imm_j_type_ID_r <= imm_j_type_id_o;
         imm_u_type_ID_r <= imm_u_type_id_o;
         zimm_rs1_type_ID_r <= zimm_rs1_type_id_o ;
         
         imm_a_mux_sel_dec_r <= imm_a_mux_sel_dec;
         imm_b_mux_sel_dec_r <= imm_b_mux_sel_dec;
         
         // ALU
         alu_operator_ID_r <= alu_operator_dec;
         alu_op_a_mux_sel_dec_r <= alu_op_a_mux_sel_dec;
         alu_op_b_mux_sel_dec_r <= alu_op_b_mux_sel_dec;
         
         // BTALU
         bt_a_mux_sel_dec_r <= bt_a_mux_sel_dec;
         bt_b_mux_sel_dec_r <= bt_b_mux_sel_dec;
         
         // MUL/DIV
         mult_en_ID_r <= mult_en;           // ==> PIPELINE
         div_en_ID_r <= div_en;           // ==> PIPELINE
         mult_sel_dec_r <= mult_sel_dec;
         div_sel_dec_r <= div_sel_dec;
         multdiv_operator_ID_r <= multdiv_operator_dec;
         multdiv_signed_mode_ID_r <= multdiv_signed_mode_dec;
         
         // REGFILE
         rf_wdata_sel_ID_r <= rf_wdata_sel;
         rf_we_ID_r <= rf_we;          // write enable for regfile
         rf_waddr_ID_r <= instr_rd;
                 
         rf_rdata_a_ID_r <= rf_rdata_a_i; 
         rf_rdata_b_ID_r <= rf_rdata_b_i; 
         
//         rf_ren_a_r <= rf_ren_a_dec;
//         rf_ren_b_r <= rf_ren_b_dec;   
         
         // CSR
         csr_access_ID_r <= csr_access_dec;
         csr_op_ID_r <= csr_op_dec;
         csr_op_en_ID_r <= csr_op_en;
        
        // LSU 
         lsu_req_ID_r <= lsu_req;
         lsu_we_ID_r <= lsu_we;
         lsu_type_ID_r <= lsu_type;
         lsu_sign_ext_ID_r <= lsu_sign_ext;
         lsu_wdata_ID_r <= lsu_wdata; 

         // WB
          instr_perf_count_id_r <= instr_perf_count_id;                 // =========> DAY VINH OI
          instr_type_wb_r <= instr_type_wb;                             // =========> DAY VINH OI
        
        end
    end
    // OUTPUT ASSIGNMENT
    // LSU INTERFACE
  assign lsu_req_EX =       lsu_req_ID_r;
  assign lsu_we_EX =        lsu_we_ID_r;
  assign lsu_type_EX =      lsu_type_ID_r;
  assign lsu_sign_ext_EX =  lsu_sign_ext_ID_r;
  assign lsu_wdata_EX =     lsu_wdata_ID_r;

  // MUL, DIV INTERFACE
  assign mult_en_EX =       mult_en_ID_r;                           // ==> PIPELINE
  assign div_en_EX =        div_en_ID_r;                            // ==> PIPELINE
  assign mult_sel_EX =      mult_sel_dec_r;                         // ==> PIPELINE
  assign div_sel_EX =       div_sel_dec_r;                          // ==> PIPELINE
  assign multdiv_operator_EX =  multdiv_operator_ID_r;              // ==> PIPELINE
  assign multdiv_signed_mode_EX = multdiv_signed_mode_ID_r;         // ==> PIPELINE
  
  // CSR
  assign csr_access_EX = csr_access_ID_r;
  assign csr_op_EX = csr_op_ID_r;
  assign csr_op_en_EX = csr_op_en_ID_r;    
  // REG_FILE
  assign rf_raddr_a_o = (use_rs3_q & ~instr_first_cycle_i) ? instr_rs3 : instr_rs1; // rs3 / rs1
  assign rf_raddr_b_o = instr_rs2; // rs2
  
  assign rf_ren_a_o = rf_ren_a_dec;
  assign rf_ren_b_o = rf_ren_b_dec;           
  
  assign rf_rdata_a_EX = rf_rdata_a_ID_r; // ==> PIPELINE
  assign rf_rdata_b_EX = rf_rdata_b_ID_r; // ==> PIPELINE
 
  assign rf_wdata_sel_EX = rf_wdata_sel_ID_r ;   // RF write data selection
  assign rf_we_EX = rf_we_ID_r;          // write enable for regfile
  assign rf_waddr_EX = rf_waddr_ID_r;
  
  // IMM
  assign imm_a_mux_sel_EX = imm_a_mux_sel_dec_r;
  assign imm_b_mux_sel_EX = imm_b_mux_sel_dec_r;
  
  assign instr_EX = instr_ID_r;
  assign instr_rs1_EX = instr_rs1_ID_r;
  assign instr_rs2_EX = instr_rs2_ID_r;
  assign instr_rs3_EX = instr_rs3_ID_r;
  assign instr_rd_EX = instr_rd_ID_r;
  assign pc_EX = pc_ID_r;
  assign instr_is_compressed_EX = instr_is_compressed_r ;
     
  assign imm_i_type_EX = imm_i_type_ID_r;
  assign imm_b_type_EX = imm_b_type_ID_r;
  assign imm_s_type_EX = imm_s_type_ID_r;
  assign imm_j_type_EX = imm_j_type_ID_r;
  assign imm_u_type_EX = imm_u_type_ID_r;
  assign zimm_rs1_type_EX = zimm_rs1_type_ID_r;
  
  // BTALU
  assign bt_a_mux_sel_EX = bt_a_mux_sel_dec_r;
  assign bt_b_mux_sel_EX = bt_b_mux_sel_dec_r;
     
  // ALU
  assign alu_operator_EX = alu_operator_ID_r;
  assign alu_op_a_mux_sel_EX = alu_op_a_mux_sel_dec_r;
  assign alu_op_b_mux_sel_EX = alu_op_b_mux_sel_dec_r;
  
  // CONTROLLER INTERFACE
  assign illegal_insn_o = illegal_insn_dec; 
  assign jump_set_o = jump_set_dec;    

    //////////// =========> DAY VINH OI
    
    assign instr_type_wb = ~lsu_req ? WB_INSTR_OTHER :
                              lsu_we      ? WB_INSTR_STORE :
                                            WB_INSTR_LOAD;
    assign instr_perf_count_id = ~ebrk_insn_o & ~ecall_insn_o & ~illegal_insn_o &
       ~instr_fetch_err_i ;
        //   &~illegal_csr_insn_i; // MAY BE FIXED
        
    assign   instr_type_wb_o = instr_type_wb_r;
    assign   instr_perf_count_id_o = instr_perf_count_id_r;
    ////////////////////////////////////////////////////////////////////

  assign mult_en_dec = mult_en;
  assign div_en_dec = div_en;
  assign lsu_we_dec = lsu_we;
  assign rf_we_dec = rf_we;


  assign lsu_req_dec = lsu_req;


endmodule
