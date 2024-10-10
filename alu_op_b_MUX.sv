//`timescale 1ns / 1ps
//////////////////////////////////////////////////////////////////////////////////
// Company: 
// Engineer: 
// 
// Create Date: 10/06/2024 06:17:39 PM
// Design Name: 
// Module Name: alu_op_b_MUX
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
module alu_op_b_MUX(
    input  logic        lsu_addr_incr_req_i,    // from LSU 
    
    input  logic        instr_is_compressed_EX, // from ID/EX pipeline
    input  logic [31:0] imm_i_type_EX,          // from ID/EX pipeline
    input  logic [31:0] imm_s_type_EX,          // from ID/EX pipeline
    input  logic [31:0] imm_u_type_EX,          // from ID/EX pipeline
    
    input  op_b_sel_e   alu_op_b_mux_sel_EX,    // from ID/EX pipeline
    input  imm_b_sel_e  imm_b_mux_sel_EX,       // from ID/EX pipeline
    input  logic [31:0] rf_rdata_b_EX,          // from ID/EX pipeline
    
    output logic [31:0] alu_operand_b_o
    );
    logic [31:0] alu_operand_b;
    logic [31:0] imm_b;
    op_b_sel_e   alu_op_b_mux_sel;
    imm_b_sel_e  imm_b_mux_sel;
    
    assign alu_op_b_mux_sel = lsu_addr_incr_req_i ? OP_B_IMM        : alu_op_b_mux_sel_EX;
    assign imm_b_mux_sel    = lsu_addr_incr_req_i ? IMM_B_INCR_ADDR : imm_b_mux_sel_EX;

    
    always_comb begin : immediate_b_mux
      unique case (imm_b_mux_sel)
        IMM_B_I:         imm_b = imm_i_type_EX;
        IMM_B_S:         imm_b = imm_s_type_EX;
        IMM_B_U:         imm_b = imm_u_type_EX;
        IMM_B_INCR_PC:   imm_b = instr_is_compressed_EX ? 32'h2 : 32'h4;
        IMM_B_INCR_ADDR: imm_b = 32'h4;
        default:         imm_b = 32'h4;
      endcase
    end
    assign alu_operand_b = (alu_op_b_mux_sel == OP_B_IMM) ? imm_b : rf_rdata_b_EX;
    assign alu_operand_b_o = alu_operand_b;
endmodule
