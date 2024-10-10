//`timescale 1ns / 1ps
//////////////////////////////////////////////////////////////////////////////////
// Company: 
// Engineer: 
// 
// Create Date: 10/06/2024 06:05:15 PM
// Design Name: 
// Module Name: alu_op_a_MUX
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

import ibex_pkg::*;
module alu_op_a_MUX(
    input  logic        lsu_addr_incr_req_i,    // from LSU
    input  logic [31:0] lsu_addr_last_i,        // from LSU
    
    input  op_a_sel_e   alu_op_a_mux_sel_EX,    // from ID/EX pipeline
    input  imm_a_sel_e  imm_a_mux_sel_EX,       // from ID/EX pipeline
    input  logic [31:0]       zimm_rs1_type_EX,       // from ID/EX pipeline
    input  logic [31:0]       rf_rdata_a_EX,          // from ID/EX pipeline
    input  logic [31:0]       pc_EX,                  // from ID/EX pipeline
    
    
    output logic [31:0] alu_operand_a_o
    );
    logic [31:0] alu_operand_a;
    logic [31:0] imm_a;
    op_a_sel_e alu_op_a_mux_sel;
    // Main ALU immediate MUX for Operand A
    // Misaligned loads/stores result in two aligned loads/stores, compute second address
  assign alu_op_a_mux_sel = lsu_addr_incr_req_i ? OP_A_FWD        : alu_op_a_mux_sel_EX;
  assign imm_a = (imm_a_mux_sel_EX == IMM_A_Z) ? zimm_rs1_type_EX : '0;

  // Main ALU MUX for Operand A
  always_comb begin : alu_operand_a_mux
    unique case (alu_op_a_mux_sel)
      OP_A_REG_A:  alu_operand_a = rf_rdata_a_EX;       // not FWD yet
      OP_A_FWD:    alu_operand_a = lsu_addr_last_i;
      OP_A_CURRPC: alu_operand_a = pc_EX;
      OP_A_IMM:    alu_operand_a = imm_a;
      default:     alu_operand_a = pc_EX;
    endcase
  end
  assign alu_operand_a_o = alu_operand_a;
endmodule
