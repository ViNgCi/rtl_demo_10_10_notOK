//`timescale 1ns / 1ps
//////////////////////////////////////////////////////////////////////////////////
// Company: 
// Engineer: 
// 
// Create Date: 08/19/2024 03:39:48 PM
// Design Name: 
// Module Name: Imm_Gen
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


module Imm_Gen (

    input logic [31:0] instr_rdata_i,
  
    output [31:0] imm_i_type_o,
    output [31:0] imm_b_type_o,
    output [31:0] imm_s_type_o,
    output [31:0] imm_j_type_o,
    output [31:0] imm_u_type_o,
    output [31:0] zimm_rs1_type_o
    
    );
    logic [31:0] instr;
    logic [4:0] instr_rs1;
    
    
    // immediate extraction and sign extension
  assign imm_i_type_o = { {20{instr[31]}}, instr[31:20] };
  assign imm_s_type_o = { {20{instr[31]}}, instr[31:25], instr[11:7] };
  assign imm_b_type_o = { {19{instr[31]}}, instr[31], instr[7], instr[30:25], instr[11:8], 1'b0 };
  assign imm_u_type_o = { instr[31:12], 12'b0 };
  assign imm_j_type_o = { {12{instr[31]}}, instr[19:12], instr[20], instr[30:21], 1'b0 };

  // immediate for CSR manipulation (zero extended)
  assign zimm_rs1_type_o = { 27'b0, instr_rs1 }; // rs1
  
  //
  assign instr = instr_rdata_i;
  assign instr_rs1 = instr[19:15];
  
  
endmodule
