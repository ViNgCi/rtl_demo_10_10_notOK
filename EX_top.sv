//`timescale 1ns / 1ps
//////////////////////////////////////////////////////////////////////////////////
// Company: 
// Engineer: 
// 
// Create Date: 10/06/2024 05:33:38 PM
// Design Name: 
// Module Name: EX_top
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


module EX_top(
    input  logic                  clk_i,
    input  logic                  rst_ni,
    // CSR RDATA
    input  logic [31:0]               csr_rdata_i,
    
    // LSU inputs
    input logic                     lsu_addr_incr_req_i,
    input logic [31:0]              lsu_addr_last_i,
    // ID/EX PIPELINE INPUT
     // MUL, DIV INTERFACE
     input logic                      mult_en_EX,           // ==> PIPELINE
     input logic                      div_en_EX,            // ==> PIPELINE
     input logic                      mult_sel_EX,          // ==> PIPELINE
     input logic                      div_sel_EX,           // ==> PIPELINE
     input ibex_pkg::md_op_e          multdiv_operator_EX,  // ==> PIPELINE
     input logic  [1:0]               multdiv_signed_mode_EX,// ==> PIPELINE
     
     input logic                      multdiv_ready_id_i,    // FSM
     input  logic                     data_ind_timing_i,     // FSM
     
     // CSR
      input logic                      csr_access_EX,
      input ibex_pkg::csr_op_e         csr_op_EX,
      input logic                      csr_op_en_EX,
      
      input  logic [31:0]              rf_rdata_a_EX, 
      input  logic [31:0]              rf_rdata_b_EX, 
      
      // WRITE
      input ibex_pkg::rf_wd_sel_e      rf_wdata_sel_EX,   // RF write data selection
      input logic                      rf_we_EX,          // write enable for regfile
      input logic [4:0]                rf_waddr_EX,
      
      // IMM
      input imm_a_sel_e                imm_a_mux_sel_EX,
      input imm_b_sel_e                imm_b_mux_sel_EX,
      
      input [31:0] instr_EX,
      input [4:0] instr_rs1_EX,
      input [4:0] instr_rs2_EX,
      input [4:0] instr_rs3_EX,
      input [4:0] instr_rd_EX,
      input [31:0] pc_EX,
      input logic instr_is_compressed_EX,
         
      input [31:0] imm_i_type_EX,
      input [31:0] imm_b_type_EX,
      input [31:0] imm_s_type_EX,
      input [31:0] imm_j_type_EX,
      input [31:0] imm_u_type_EX,
      input [31:0] zimm_rs1_type_EX,
      
      // BTALU
      input op_a_sel_e                 bt_a_mux_sel_EX,
      input imm_b_sel_e                bt_b_mux_sel_EX,
         
      // ALU
      input   alu_op_e                 alu_operator_EX,
      input   op_a_sel_e               alu_op_a_mux_sel_EX,
      input   op_b_sel_e               alu_op_b_mux_sel_EX,
      input   logic                    alu_instr_first_cycle_i,
      

     
      // Outputs
      output logic [31:0]           alu_adder_result_ex_o, // to LSU
      output logic [31:0]           branch_target_o,       // to IF
      output logic                  branch_decision_o,     // to ID
    
      output logic                  ex_valid_o,             // EX has valid output
      //
      output logic [4:0]                rf_waddr_EX_o,      // ==> EX/WB 
      output logic [31:0]               rf_wdata_EX_o,      // ==> EX/WB
      output logic                      rf_we_EX_o          // ==> EX/WB
        
      // output logic [31:0]           lsu_wdata_EX_o        // to LSU
    
    );

          // intermediate val reg
    logic [33:0]          imd_val_q_i[2];
    logic [1:0]            imd_val_we_o;
    logic [33:0]           imd_val_d_o[2];
    logic [33:0]           imd_val_q[2];

    // assign rf_waddr_EX_o = rf_rdata_b_EX;
    
    //////////////////
    // Operands MUX //
    /////////////////
    logic [31:0]           alu_operand_a;
    logic [31:0]           alu_operand_b;
    
    logic [31:0]           bt_a_operand;
    logic [31:0]           bt_b_operand;
    logic [31:0]           result_ex_o;
    alu_op_a_MUX alu_opa_mux(
    .lsu_addr_incr_req_i(lsu_addr_incr_req_i),    // from LSU
    .lsu_addr_last_i(lsu_addr_last_i),        // from LSU
    
    .alu_op_a_mux_sel_EX(alu_op_a_mux_sel_EX),    // from ID/EX pipeline
    .imm_a_mux_sel_EX(imm_a_mux_sel_EX),       // from ID/EX pipeline
    .zimm_rs1_type_EX(zimm_rs1_type_EX),       // from ID/EX pipeline
    .rf_rdata_a_EX(rf_rdata_a_EX),          // from ID/EX pipeline
    .pc_EX(pc_EX),                  // from ID/EX pipeline
    
    .alu_operand_a_o(alu_operand_a)
    );
    
    alu_op_b_MUX alu_opb_mux(
    .lsu_addr_incr_req_i(lsu_addr_incr_req_i),    // from LSU 
    
    .instr_is_compressed_EX(instr_is_compressed_EX), // from ID/EX pipeline
    .imm_i_type_EX(imm_i_type_EX),          // from ID/EX pipeline
    .imm_s_type_EX(imm_s_type_EX),          // from ID/EX pipeline
    .imm_u_type_EX(imm_u_type_EX),          // from ID/EX pipeline
    
    .alu_op_b_mux_sel_EX(alu_op_b_mux_sel_EX),    // from ID/EX pipeline
    .imm_b_mux_sel_EX(imm_b_mux_sel_EX),       // from ID/EX pipeline
    .rf_rdata_b_EX(rf_rdata_b_EX),          // from ID/EX pipeline
    
    .alu_operand_b_o(alu_operand_b)
    );
    
    BTALU_MUX bt_alu_mux(
    .imm_i_type_EX(imm_i_type_EX),          // from ID/EX pipeline
    .imm_b_type_EX(imm_b_type_EX),          // from ID/EX pipeline
    .imm_j_type_EX(imm_j_type_EX),          // from ID/EX pipeline 
    .instr_is_compressed_EX(instr_is_compressed_EX), // from ID/EX pipeline
    .bt_a_mux_sel_EX(bt_a_mux_sel_EX),        // from ID/EX pipeline
    .bt_b_mux_sel_EX(bt_b_mux_sel_EX),        // from ID/EX pipeline
    .rf_rdata_a_EX(rf_rdata_a_EX),          // from ID/EX pipeline
    .pc_EX(pc_EX),                  // from ID/EX pipeline
    
    .bt_a_operand_o(bt_a_operand),
    .bt_b_operand_o(bt_b_operand)
    );
   //
   logic [31:0] alu_result, multdiv_result;
   logic        alu_cmp_result, alu_is_equal_result;
   
   logic [32:0] multdiv_alu_operand_b, multdiv_alu_operand_a;
   logic multdiv_sel ;
   assign multdiv_sel = mult_sel_EX | div_sel_EX;
   logic [33:0] alu_adder_result_ext;
   
   logic [31:0] alu_imd_val_q[2];
   logic [31:0] alu_imd_val_d[2];
   logic [ 1:0] alu_imd_val_we;
   logic [33:0] multdiv_imd_val_d[2];
   logic [ 1:0] multdiv_imd_val_we;
   
   // Intermediate Value Register Mux
  assign imd_val_d_o[0] = multdiv_sel ? multdiv_imd_val_d[0] : {2'b0, alu_imd_val_d[0]};
  assign imd_val_d_o[1] = multdiv_sel ? multdiv_imd_val_d[1] : {2'b0, alu_imd_val_d[1]};
  assign imd_val_we_o   = multdiv_sel ? multdiv_imd_val_we : alu_imd_val_we;

  assign alu_imd_val_q = '{imd_val_q_i[0][31:0], imd_val_q_i[1][31:0]};

  assign result_ex_o  = multdiv_sel ? multdiv_result : alu_result;

    /////////////////////////////////////////
  // Multicycle Operation Stage Register //
  /////////////////////////////////////////

  for (genvar i = 0; i < 2; i++) begin : gen_intermediate_val_reg
    always_ff @(posedge clk_i or negedge rst_ni) begin : intermediate_val_reg
      if (!rst_ni) begin
        imd_val_q[i] <= '0;
      end else if (imd_val_we_o[i]) begin
        imd_val_q[i] <= imd_val_d_o[i];
      end
    end
  end

  assign imd_val_q_i = imd_val_q;
   
   
    
   ALU u_alu(
  .operator_i(alu_operator_EX),
  .operand_a_i(alu_operand_a),
  .operand_b_i(alu_operand_b),
  .instr_first_cycle_i(alu_instr_first_cycle_i),
  .multdiv_operand_a_i(multdiv_alu_operand_a),    // from MUL/DIV
  .multdiv_operand_b_i(multdiv_alu_operand_b),    // from MUL/DIV
  .multdiv_sel_i(multdiv_sel),          
  .imd_val_q_i(alu_imd_val_q),
  .imd_val_d_o(alu_imd_val_d),
  .imd_val_we_o(alu_imd_val_we),
  .adder_result_o(alu_adder_result_ex_o),
  .adder_result_ext_o(alu_adder_result_ext),
  .result_o(alu_result),
  .comparison_result_o(alu_cmp_result),
  .is_equal_result_o(alu_is_equal_result)  
);

  ////////////////
  // Multiplier //
  ////////////////
    logic [31:0]               multdiv_operand_a;  
    logic [31:0]               multdiv_operand_b; 
    
    logic        multdiv_valid;
    
    assign multdiv_operand_a = rf_rdata_a_EX;
    assign multdiv_operand_b = rf_rdata_b_EX;
    ibex_multdiv_fast multdiv_i 
    (
      .clk_i             (clk_i),
      .rst_ni            (rst_ni),
      .mult_en_i         (mult_en_EX),
      .div_en_i          (div_en_EX),
      .mult_sel_i        (mult_sel_EX),
      .div_sel_i         (div_sel_EX),
      .operator_i        (multdiv_operator_EX),
      .signed_mode_i     (multdiv_signed_mode_EX),
      .op_a_i            (multdiv_operand_a),
      .op_b_i            (multdiv_operand_b),
      .alu_operand_a_o   (multdiv_alu_operand_a),
      .alu_operand_b_o   (multdiv_alu_operand_b),
      .alu_adder_ext_i   (alu_adder_result_ext),
      .alu_adder_i       (alu_adder_result_ex_o),
      .equal_to_zero_i   (alu_is_equal_result),
      .data_ind_timing_i (data_ind_timing_i),
      .imd_val_q_i       (imd_val_q_i),
      .imd_val_d_o       (multdiv_imd_val_d),
      .imd_val_we_o      (multdiv_imd_val_we),
      .multdiv_ready_id_i(multdiv_ready_id_i),
      .valid_o           (multdiv_valid),
      .multdiv_result_o  (multdiv_result)
    );

    // Multiplier/divider may require multiple cycles. The ALU output is valid in the same cycle
  // unless the intermediate result register is being written (which indicates this isn't the
  // final cycle of ALU operation).
  assign ex_valid_o = multdiv_sel ? multdiv_valid : ~(|alu_imd_val_we);
  
  // branch handling
  assign branch_decision_o  = alu_cmp_result;

    logic [32:0] bt_alu_result;
    logic        unused_bt_carry;

    assign bt_alu_result   = bt_a_operand + bt_b_operand;

    assign unused_bt_carry = bt_alu_result[32];
    assign branch_target_o = bt_alu_result[31:0];
  
   // Register file write data mux
  always_comb begin : rf_wdata_id_mux
    unique case (rf_wdata_sel_EX)
      RF_WD_EX:  rf_wdata_EX_o = result_ex_o;
      RF_WD_CSR: rf_wdata_EX_o = csr_rdata_i;
      default:   rf_wdata_EX_o = result_ex_o;
    endcase
  end
  assign rf_waddr_EX_o = rf_waddr_EX;
  assign rf_we_EX_o = rf_we_EX;
endmodule
