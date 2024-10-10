//`timescale 1ns / 1ps
//////////////////////////////////////////////////////////////////////////////////
// Company: 
// Engineer: 
// 
// Create Date: 10/06/2024 06:33:11 PM
// Design Name: 
// Module Name: BTALU_MUX
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
module BTALU_MUX(

    input  logic [31:0] imm_i_type_EX,          // from ID/EX pipeline
    input  logic [31:0] imm_b_type_EX,          // from ID/EX pipeline
    input  logic [31:0] imm_j_type_EX,          // from ID/EX pipeline 
    input  logic        instr_is_compressed_EX, // from ID/EX pipeline
    input  op_a_sel_e   bt_a_mux_sel_EX,        // from ID/EX pipeline
    input  imm_b_sel_e  bt_b_mux_sel_EX,        // from ID/EX pipeline
    input  logic [31:0] rf_rdata_a_EX,          // from ID/EX pipeline
    input  logic [31:0] pc_EX,                  // from ID/EX pipeline
    
    output logic [31:0]     bt_a_operand_o,
    output logic [31:0]     bt_b_operand_o
    );
    
    logic [31:0]     bt_a_operand;
    logic [31:0]     bt_b_operand;
    // Branch target ALU operand A mux
    always_comb begin : bt_operand_a_mux
      unique case (bt_a_mux_sel_EX)
        OP_A_REG_A:  bt_a_operand = rf_rdata_a_EX;
        OP_A_CURRPC: bt_a_operand = pc_EX;
        default:     bt_a_operand = pc_EX;
      endcase
    end

    // Branch target ALU operand B mux
    always_comb begin : bt_immediate_b_mux
      unique case (bt_b_mux_sel_EX)
        IMM_B_I:         bt_b_operand = imm_i_type_EX;
        IMM_B_B:         bt_b_operand = imm_b_type_EX;
        IMM_B_J:         bt_b_operand = imm_j_type_EX;
        IMM_B_INCR_PC:   bt_b_operand = instr_is_compressed_EX ? 32'h2 : 32'h4;
        default:         bt_b_operand = instr_is_compressed_EX ? 32'h2 : 32'h4;
      endcase
    end
    assign bt_a_operand_o = bt_a_operand;
    assign bt_b_operand_o = bt_b_operand;
endmodule
