//`timescale 1ns / 1ps
//////////////////////////////////////////////////////////////////////////////////
// Company: 
// Engineer: 
// 
// Create Date: 09/06/2024 07:25:04 PM
// Design Name: 
// Module Name: alu_decoder
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
module alu_decoder #(
  parameter bit RV32E               = 0,
  parameter rv32m_e RV32M = RV32MFast,
  parameter rv32b_e RV32B = RV32BNone,
  parameter bit BranchTargetALU     = 0
)
(   
  input  logic                 clk_i,
  input  logic                 rst_ni,
  
  input  logic                 instr_first_cycle_i,
  input  logic [31:0]          instr_rdata_alu_i,
  
  input  logic                  branch_taken_i,
  
                    
    // ALU
  output alu_op_e    alu_operator_o,        // ALU operation selection
  output op_a_sel_e  alu_op_a_mux_sel_o,    // operand a selection: reg value, PC,
                                                      // immediate or zero
  output op_b_sel_e  alu_op_b_mux_sel_o,    // operand b selection: reg value or
                                                      // immediate
  output logic                 alu_multicycle_o,      // ternary bitmanip instruction
  
  // immediates 
  output imm_a_sel_e  imm_a_mux_sel_o,       // immediate selection for operand a
  output imm_b_sel_e  imm_b_mux_sel_o,       // immediate selection for operand b
  output op_a_sel_e   bt_a_mux_sel_o,        // branch target selection operand a
  output imm_b_sel_e  bt_b_mux_sel_o,        // branch target selection operand b
  
  output logic                 mult_sel_o,            // as above but static, for data muxes
  output logic                 div_sel_o,             // as above but static, for data muxes
  output logic                 use_rs3_q                

    );
   
    logic [31:0] instr_alu;
    opcode_e     opcode_alu;
    logic        use_rs3_d;
    assign instr_alu = instr_rdata_alu_i;
    
always_comb begin
    alu_operator_o     = ALU_SLTU;
    alu_op_a_mux_sel_o = OP_A_IMM;
    alu_op_b_mux_sel_o = OP_B_IMM;

    imm_a_mux_sel_o    = IMM_A_ZERO;
    imm_b_mux_sel_o    = IMM_B_I;

    bt_a_mux_sel_o     = OP_A_CURRPC;
    bt_b_mux_sel_o     = IMM_B_I;


    opcode_alu         = opcode_e'(instr_alu[6:0]);

    use_rs3_d          = 1'b0;
    alu_multicycle_o   = 1'b0;
    mult_sel_o         = 1'b0;
    div_sel_o          = 1'b0;

    unique case (opcode_alu)

      ///////////
      // Jumps //
      ///////////

      OPCODE_JAL: begin // Jump and Link
          bt_a_mux_sel_o = OP_A_CURRPC;
          bt_b_mux_sel_o = IMM_B_J;
        
          // Calculate and store PC+4
          alu_op_a_mux_sel_o  = OP_A_CURRPC;
          alu_op_b_mux_sel_o  = OP_B_IMM;
          imm_b_mux_sel_o     = IMM_B_INCR_PC;
          alu_operator_o      = ALU_ADD;
        
      end

      OPCODE_JALR: begin // Jump and Link Register
          // Calculate ??a ch? Jump s? d?ng BTALU
          bt_a_mux_sel_o = OP_A_REG_A;
          bt_b_mux_sel_o = IMM_B_I;
          // ALU chính ch? c?n tính toán và l?u ??a ch? PC+4
          // Calculate and store PC+4
          alu_op_a_mux_sel_o  = OP_A_CURRPC;
          alu_op_b_mux_sel_o  = OP_B_IMM;
          imm_b_mux_sel_o     = IMM_B_INCR_PC;
          alu_operator_o      = ALU_ADD;
        
      end

      OPCODE_BRANCH: begin // Branch
        // Check branch condition selection
        unique case (instr_alu[14:12])
          3'b000:  alu_operator_o = ALU_EQ;
          3'b001:  alu_operator_o = ALU_NE;
          3'b100:  alu_operator_o = ALU_LT;
          3'b101:  alu_operator_o = ALU_GE;
          3'b110:  alu_operator_o = ALU_LTU;
          3'b111:  alu_operator_o = ALU_GEU;
          default: ;
        endcase
        // Using BTALU ==> branch target & branch decision ???c tính toán trong 1 cycle
        // CALCULATE branch target
          bt_a_mux_sel_o = OP_A_CURRPC;
          // Not-taken branch will jump to next instruction (used in secure mode)
          bt_b_mux_sel_o = branch_taken_i ? IMM_B_B : IMM_B_INCR_PC;
        // Mux select ?? ch?n 2 operant ?? check branch condition
          alu_op_a_mux_sel_o  = OP_A_REG_A;
          alu_op_b_mux_sel_o  = OP_B_REG_B;
         
      end

      ////////////////
      // Load/store //
      ////////////////

      OPCODE_STORE: begin
        alu_op_a_mux_sel_o = OP_A_REG_A;
        alu_op_b_mux_sel_o = OP_B_REG_B;
        alu_operator_o     = ALU_ADD;

        if (!instr_alu[14]) begin
          // offset from immediate
          imm_b_mux_sel_o     = IMM_B_S;
          alu_op_b_mux_sel_o  = OP_B_IMM;
        end
      end

      OPCODE_LOAD: begin
        alu_op_a_mux_sel_o  = OP_A_REG_A;

        // offset from immediate
        alu_operator_o      = ALU_ADD;
        alu_op_b_mux_sel_o  = OP_B_IMM;
        imm_b_mux_sel_o     = IMM_B_I;
      end

      /////////
      // ALU //
      /////////

      OPCODE_LUI: begin  // Load Upper Immediate
        alu_op_a_mux_sel_o  = OP_A_IMM;
        alu_op_b_mux_sel_o  = OP_B_IMM;
        imm_a_mux_sel_o     = IMM_A_ZERO;
        imm_b_mux_sel_o     = IMM_B_U;
        alu_operator_o      = ALU_ADD;
      end

      OPCODE_AUIPC: begin  // Add Upper Immediate to PC
        alu_op_a_mux_sel_o  = OP_A_CURRPC;
        alu_op_b_mux_sel_o  = OP_B_IMM;
        imm_b_mux_sel_o     = IMM_B_U;
        alu_operator_o      = ALU_ADD;
      end

      OPCODE_OP_IMM: begin // Register-Immediate ALU Operations
        alu_op_a_mux_sel_o  = OP_A_REG_A;
        alu_op_b_mux_sel_o  = OP_B_IMM;
        imm_b_mux_sel_o     = IMM_B_I;

        unique case (instr_alu[14:12])
          3'b000: alu_operator_o = ALU_ADD;  // Add Immediate
          3'b010: alu_operator_o = ALU_SLT;  // Set to one if Lower Than Immediate
          3'b011: alu_operator_o = ALU_SLTU; // Set to one if Lower Than Immediate Unsigned
          3'b100: alu_operator_o = ALU_XOR;  // Exclusive Or with Immediate
          3'b110: alu_operator_o = ALU_OR;   // Or with Immediate
          3'b111: alu_operator_o = ALU_AND;  // And with Immediate

          3'b001: begin
            if (RV32B != RV32BNone) begin
              unique case (instr_alu[31:27])
                5'b0_0000: alu_operator_o = ALU_SLL;    // Shift Left Logical by Immediate
                // Shift Left Ones by Immediate
                5'b0_0100: begin
                  if (RV32B == RV32BOTEarlGrey || RV32B == RV32BFull) alu_operator_o = ALU_SLO;
                end
                5'b0_1001: alu_operator_o = ALU_BCLR; // Clear bit specified by immediate
                5'b0_0101: alu_operator_o = ALU_BSET; // Set bit specified by immediate
                5'b0_1101: alu_operator_o = ALU_BINV; // Invert bit specified by immediate.
                // Shuffle with Immediate Control Value
                5'b0_0001: if (instr_alu[26] == 0) alu_operator_o = ALU_SHFL;
                5'b0_1100: begin
                  unique case (instr_alu[26:20])
                    7'b000_0000: alu_operator_o = ALU_CLZ;   // clz
                    7'b000_0001: alu_operator_o = ALU_CTZ;   // ctz
                    7'b000_0010: alu_operator_o = ALU_CPOP;  // cpop
                    7'b000_0100: alu_operator_o = ALU_SEXTB; // sext.b
                    7'b000_0101: alu_operator_o = ALU_SEXTH; // sext.h
                    7'b001_0000: begin
                      if (RV32B == RV32BOTEarlGrey || RV32B == RV32BFull) begin
                        alu_operator_o = ALU_CRC32_B;  // crc32.b
                        alu_multicycle_o = 1'b1;
                      end
                    end
                    7'b001_0001: begin
                      if (RV32B == RV32BOTEarlGrey || RV32B == RV32BFull) begin
                        alu_operator_o = ALU_CRC32_H;  // crc32.h
                        alu_multicycle_o = 1'b1;
                      end
                    end
                    7'b001_0010: begin
                      if (RV32B == RV32BOTEarlGrey || RV32B == RV32BFull) begin
                        alu_operator_o = ALU_CRC32_W;  // crc32.w
                        alu_multicycle_o = 1'b1;
                      end
                    end
                    7'b001_1000: begin
                      if (RV32B == RV32BOTEarlGrey || RV32B == RV32BFull) begin
                        alu_operator_o = ALU_CRC32C_B; // crc32c.b
                        alu_multicycle_o = 1'b1;
                      end
                    end
                    7'b001_1001: begin
                      if (RV32B == RV32BOTEarlGrey || RV32B == RV32BFull) begin
                        alu_operator_o = ALU_CRC32C_H; // crc32c.h
                        alu_multicycle_o = 1'b1;
                      end
                    end
                    7'b001_1010: begin
                      if (RV32B == RV32BOTEarlGrey || RV32B == RV32BFull) begin
                        alu_operator_o = ALU_CRC32C_W; // crc32c.w
                        alu_multicycle_o = 1'b1;
                      end
                    end
                    default: ;
                  endcase
                end

                default: ;
              endcase
            end else begin
              alu_operator_o = ALU_SLL; // Shift Left Logical by Immediate
            end
          end

          3'b101: begin
            if (RV32B != RV32BNone) begin
              if (instr_alu[26] == 1'b1) begin
                alu_operator_o = ALU_FSR;
                alu_multicycle_o = 1'b1;
                if (instr_first_cycle_i) begin
                  use_rs3_d = 1'b1;
                end else begin
                  use_rs3_d = 1'b0;
                end
              end else begin
                unique case (instr_alu[31:27])
                  5'b0_0000: alu_operator_o = ALU_SRL;   // Shift Right Logical by Immediate
                  5'b0_1000: alu_operator_o = ALU_SRA;   // Shift Right Arithmetically by Immediate
                  // Shift Right Ones by Immediate
                  5'b0_0100: begin
                    if (RV32B == RV32BOTEarlGrey || RV32B == RV32BFull) alu_operator_o = ALU_SRO;
                  end
                  5'b0_1001: alu_operator_o = ALU_BEXT;  // Extract bit specified by immediate.
                  5'b0_1100: begin
                    alu_operator_o = ALU_ROR;            // Rotate Right by Immediate
                    alu_multicycle_o = 1'b1;
                  end
                  5'b0_1101: alu_operator_o = ALU_GREV;  // General Reverse with Imm Control Val
                  5'b0_0101: alu_operator_o = ALU_GORC;  // General Or-combine with Imm Control Val
                  // Unshuffle with Immediate Control Value
                  5'b0_0001: begin
                    if (RV32B == RV32BOTEarlGrey || RV32B == RV32BFull) begin
                      if (instr_alu[26] == 1'b0) alu_operator_o = ALU_UNSHFL;
                    end
                  end
                  default: ;
                endcase
              end

            end else begin
              if (instr_alu[31:27] == 5'b0_0000) begin
                alu_operator_o = ALU_SRL;               // Shift Right Logical by Immediate
              end else if (instr_alu[31:27] == 5'b0_1000) begin
                alu_operator_o = ALU_SRA;               // Shift Right Arithmetically by Immediate
              end
            end
          end

          default: ;
        endcase
      end

      OPCODE_OP: begin  // Register-Register ALU operation
        alu_op_a_mux_sel_o = OP_A_REG_A;
        alu_op_b_mux_sel_o = OP_B_REG_B;

        if (instr_alu[26]) begin
          if (RV32B != RV32BNone) begin
            unique case ({instr_alu[26:25], instr_alu[14:12]})
              {2'b11, 3'b001}: begin
                alu_operator_o   = ALU_CMIX; // cmix
                alu_multicycle_o = 1'b1;
                if (instr_first_cycle_i) begin
                  use_rs3_d = 1'b1;
                end else begin
                  use_rs3_d = 1'b0;
                end
              end
              {2'b11, 3'b101}: begin
                alu_operator_o   = ALU_CMOV; // cmov
                alu_multicycle_o = 1'b1;
                if (instr_first_cycle_i) begin
                  use_rs3_d = 1'b1;
                end else begin
                  use_rs3_d = 1'b0;
                end
              end
              {2'b10, 3'b001}: begin
                alu_operator_o   = ALU_FSL;  // fsl
                alu_multicycle_o = 1'b1;
                if (instr_first_cycle_i) begin
                  use_rs3_d = 1'b1;
                end else begin
                  use_rs3_d = 1'b0;
                end
              end
              {2'b10, 3'b101}: begin
                alu_operator_o   = ALU_FSR;  // fsr
                alu_multicycle_o = 1'b1;
                if (instr_first_cycle_i) begin
                  use_rs3_d = 1'b1;
                end else begin
                  use_rs3_d = 1'b0;
                end
              end
              default: ;
            endcase
          end
        end else begin
          unique case ({instr_alu[31:25], instr_alu[14:12]})
            // RV32I ALU operations
            {7'b000_0000, 3'b000}: alu_operator_o = ALU_ADD;   // Add
            {7'b010_0000, 3'b000}: alu_operator_o = ALU_SUB;   // Sub
            {7'b000_0000, 3'b010}: alu_operator_o = ALU_SLT;   // Set Lower Than
            {7'b000_0000, 3'b011}: alu_operator_o = ALU_SLTU;  // Set Lower Than Unsigned
            {7'b000_0000, 3'b100}: alu_operator_o = ALU_XOR;   // Xor
            {7'b000_0000, 3'b110}: alu_operator_o = ALU_OR;    // Or
            {7'b000_0000, 3'b111}: alu_operator_o = ALU_AND;   // And
            {7'b000_0000, 3'b001}: alu_operator_o = ALU_SLL;   // Shift Left Logical
            {7'b000_0000, 3'b101}: alu_operator_o = ALU_SRL;   // Shift Right Logical
            {7'b010_0000, 3'b101}: alu_operator_o = ALU_SRA;   // Shift Right Arithmetic

            // RV32B ALU Operations
            {7'b011_0000, 3'b001}: begin
              if (RV32B != RV32BNone) begin
                alu_operator_o = ALU_ROL;
                alu_multicycle_o = 1'b1;
              end
            end
            {7'b011_0000, 3'b101}: begin
              if (RV32B != RV32BNone) begin
                alu_operator_o = ALU_ROR;
                alu_multicycle_o = 1'b1;
              end
            end

            {7'b000_0101, 3'b100}: if (RV32B != RV32BNone) alu_operator_o = ALU_MIN;
            {7'b000_0101, 3'b110}: if (RV32B != RV32BNone) alu_operator_o = ALU_MAX;
            {7'b000_0101, 3'b101}: if (RV32B != RV32BNone) alu_operator_o = ALU_MINU;
            {7'b000_0101, 3'b111}: if (RV32B != RV32BNone) alu_operator_o = ALU_MAXU;

            {7'b000_0100, 3'b100}: if (RV32B != RV32BNone) alu_operator_o = ALU_PACK;
            {7'b010_0100, 3'b100}: if (RV32B != RV32BNone) alu_operator_o = ALU_PACKU;
            {7'b000_0100, 3'b111}: if (RV32B != RV32BNone) alu_operator_o = ALU_PACKH;

            {7'b010_0000, 3'b100}: if (RV32B != RV32BNone) alu_operator_o = ALU_XNOR;
            {7'b010_0000, 3'b110}: if (RV32B != RV32BNone) alu_operator_o = ALU_ORN;
            {7'b010_0000, 3'b111}: if (RV32B != RV32BNone) alu_operator_o = ALU_ANDN;

            // RV32B zba
            {7'b001_0000, 3'b010}: if (RV32B != RV32BNone) alu_operator_o = ALU_SH1ADD;
            {7'b001_0000, 3'b100}: if (RV32B != RV32BNone) alu_operator_o = ALU_SH2ADD;
            {7'b001_0000, 3'b110}: if (RV32B != RV32BNone) alu_operator_o = ALU_SH3ADD;

            // RV32B zbs
            {7'b010_0100, 3'b001}: if (RV32B != RV32BNone) alu_operator_o = ALU_BCLR;
            {7'b001_0100, 3'b001}: if (RV32B != RV32BNone) alu_operator_o = ALU_BSET;
            {7'b011_0100, 3'b001}: if (RV32B != RV32BNone) alu_operator_o = ALU_BINV;
            {7'b010_0100, 3'b101}: if (RV32B != RV32BNone) alu_operator_o = ALU_BEXT;

            // RV32B zbf
            {7'b010_0100, 3'b111}: if (RV32B != RV32BNone) alu_operator_o = ALU_BFP;

            // RV32B zbp
            {7'b011_0100, 3'b101}: if (RV32B != RV32BNone) alu_operator_o = ALU_GREV;
            {7'b001_0100, 3'b101}: if (RV32B != RV32BNone) alu_operator_o = ALU_GORC;
            {7'b000_0100, 3'b001}: begin
              if (RV32B == RV32BOTEarlGrey || RV32B == RV32BFull) alu_operator_o = ALU_SHFL;
            end
            {7'b000_0100, 3'b101}: begin
              if (RV32B == RV32BOTEarlGrey || RV32B == RV32BFull) alu_operator_o = ALU_UNSHFL;
            end
            {7'b001_0100, 3'b010}: begin
              if (RV32B == RV32BOTEarlGrey || RV32B == RV32BFull) alu_operator_o = ALU_XPERM_N;
            end
            {7'b001_0100, 3'b100}: begin
              if (RV32B == RV32BOTEarlGrey || RV32B == RV32BFull) alu_operator_o = ALU_XPERM_B;
            end
            {7'b001_0100, 3'b110}: begin
              if (RV32B == RV32BOTEarlGrey || RV32B == RV32BFull) alu_operator_o = ALU_XPERM_H;
            end
            {7'b001_0000, 3'b001}: begin
              if (RV32B == RV32BOTEarlGrey || RV32B == RV32BFull) alu_operator_o = ALU_SLO;
            end
            {7'b001_0000, 3'b101}: begin
              if (RV32B == RV32BOTEarlGrey || RV32B == RV32BFull) alu_operator_o = ALU_SRO;
            end

            // RV32B zbc
            {7'b000_0101, 3'b001}: begin
              if (RV32B == RV32BOTEarlGrey || RV32B == RV32BFull) alu_operator_o = ALU_CLMUL;
            end
            {7'b000_0101, 3'b010}: begin
              if (RV32B == RV32BOTEarlGrey || RV32B == RV32BFull) alu_operator_o = ALU_CLMULR;
            end
            {7'b000_0101, 3'b011}: begin
              if (RV32B == RV32BOTEarlGrey || RV32B == RV32BFull) alu_operator_o = ALU_CLMULH;
            end

            // RV32B zbe
            {7'b010_0100, 3'b110}: begin
              if (RV32B == RV32BFull) begin
                alu_operator_o = ALU_BDECOMPRESS;
                alu_multicycle_o = 1'b1;
              end
            end
            {7'b000_0100, 3'b110}: begin
              if (RV32B == RV32BFull) begin
                alu_operator_o = ALU_BCOMPRESS;
                alu_multicycle_o = 1'b1;
              end
            end

            // RV32M instructions, all use the same ALU operation
            {7'b000_0001, 3'b000}: begin // mul
              alu_operator_o = ALU_ADD;
              mult_sel_o     = (RV32M == RV32MNone) ? 1'b0 : 1'b1;
            end
            {7'b000_0001, 3'b001}: begin // mulh
              alu_operator_o = ALU_ADD;
              mult_sel_o     = (RV32M == RV32MNone) ? 1'b0 : 1'b1;
            end
            {7'b000_0001, 3'b010}: begin // mulhsu
              alu_operator_o = ALU_ADD;
              mult_sel_o     = (RV32M == RV32MNone) ? 1'b0 : 1'b1;
            end
            {7'b000_0001, 3'b011}: begin // mulhu
              alu_operator_o = ALU_ADD;
              mult_sel_o     = (RV32M == RV32MNone) ? 1'b0 : 1'b1;
            end
            {7'b000_0001, 3'b100}: begin // div
              alu_operator_o = ALU_ADD;
              div_sel_o      = (RV32M == RV32MNone) ? 1'b0 : 1'b1;
            end
            {7'b000_0001, 3'b101}: begin // divu
              alu_operator_o = ALU_ADD;
              div_sel_o      = (RV32M == RV32MNone) ? 1'b0 : 1'b1;
            end
            {7'b000_0001, 3'b110}: begin // rem
              alu_operator_o = ALU_ADD;
              div_sel_o      = (RV32M == RV32MNone) ? 1'b0 : 1'b1;
            end
            {7'b000_0001, 3'b111}: begin // remu
              alu_operator_o = ALU_ADD;
              div_sel_o      = (RV32M == RV32MNone) ? 1'b0 : 1'b1;
            end

            default: ;
          endcase
        end
      end

      /////////////
      // Special //
      /////////////

      OPCODE_MISC_MEM: begin
        unique case (instr_alu[14:12])
          3'b000: begin
            // FENCE is treated as a NOP since all memory operations are already strictly ordered.
            alu_operator_o     = ALU_ADD; // nop
            alu_op_a_mux_sel_o = OP_A_REG_A;
            alu_op_b_mux_sel_o = OP_B_IMM;
          end
          3'b001: begin
            // FENCE.I will flush the IF stage, prefetch buffer and ICache if present.
            if (BranchTargetALU) begin
              bt_a_mux_sel_o     = OP_A_CURRPC;
              bt_b_mux_sel_o     = IMM_B_INCR_PC;
            end else begin
              alu_op_a_mux_sel_o = OP_A_CURRPC;
              alu_op_b_mux_sel_o = OP_B_IMM;
              imm_b_mux_sel_o    = IMM_B_INCR_PC;
              alu_operator_o     = ALU_ADD;
            end
          end
          default: ;
        endcase
      end

      OPCODE_SYSTEM: begin
        if (instr_alu[14:12] == 3'b000) begin
          // non CSR related SYSTEM instructions
          alu_op_a_mux_sel_o = OP_A_REG_A;
          alu_op_b_mux_sel_o = OP_B_IMM;
        end else begin
          // instruction to read/modify CSR
          alu_op_b_mux_sel_o = OP_B_IMM;
          imm_a_mux_sel_o    = IMM_A_Z;
          imm_b_mux_sel_o    = IMM_B_I;  // CSR address is encoded in I imm

          if (instr_alu[14]) begin
            // rs1 field is used as immediate
            alu_op_a_mux_sel_o = OP_A_IMM;
          end else begin
            alu_op_a_mux_sel_o = OP_A_REG_A;
          end
        end

      end
      default: ;
    endcase
  end
  

    // the use of rs3 is known one cycle ahead.
    always_ff  @(posedge clk_i or negedge rst_ni) begin
      if (!rst_ni) begin
        use_rs3_q <= 1'b0;
      end else begin
        use_rs3_q <= use_rs3_d;
      end
    end
endmodule
