//`timescale 1ns / 1ps
//////////////////////////////////////////////////////////////////////////////////
// Company: 
// Engineer: 
// 
// Create Date: 09/19/2024 09:13:48 PM
// Design Name: 
// Module Name: instr_decoder
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


module instr_decoder #(
  parameter bit RV32E               = 0,
  parameter ibex_pkg::rv32m_e RV32M = ibex_pkg::RV32MFast,
  parameter ibex_pkg::rv32b_e RV32B = ibex_pkg::RV32BNone,
  parameter bit BranchTargetALU     = 1
) (

  input  logic                 clk_i,
  input  logic                 rst_ni,
    
    // from IF-ID pipeline register
  input  logic                 instr_first_cycle_i,   // instruction read is in its first cycle
  input  logic [31:0]          instr_rdata_i,         // instruction read from memory/cache

  input  logic                 illegal_c_insn_i,      // compressed instruction decode failed
  
  //  CONTROLLER INTERFACE
  output logic                 illegal_insn_o,        // illegal instr encountered
  output logic                 ebrk_insn_o,           // trap instr encountered
  output logic                 mret_insn_o,           // return from exception instr
                                                      // encountered
  output logic                 dret_insn_o,           // return from debug instr encountered
  output logic                 ecall_insn_o,          // syscall instr encountered
  output logic                 wfi_insn_o,            // wait for interrupt instr encountered
  output logic                 jump_set_o,            // jump taken set signal
  output logic                 icache_inval_o,
  
  // REG_FILE INTERFACE
  output ibex_pkg::rf_wd_sel_e rf_wdata_sel_o,   // RF write data selection BETWEEN CSR AND ALU_MULT/DIV
  output logic                 rf_ren_a_o,          // Instruction reads from RF addr A // only for REG_FILE ECC
  output logic                 rf_ren_b_o,          // Instruction reads from RF addr B // only for REG_FILE ECC
  
  output ibex_pkg::md_op_e     multdiv_operator_o,          // INSTR_DECODER
  output logic [1:0]           multdiv_signed_mode_o,       // INSTR_DECODER
  
  // CSRs
  output logic                 csr_access_o,          // access to CSR
  output ibex_pkg::csr_op_e    csr_op_o,              // operation to perform on CSR

  // LSU
  output logic                 data_req_o,            // start transaction to data memory
  output logic                 data_we_o,             // write enable
  output logic [1:0]           data_type_o,           // size of transaction: byte, half
                                                      // word or word
  output logic                 data_sign_extension_o, // sign extension for data read from
                                                      // memory

  // jump/branches
  output logic                 jump_in_dec_o,         // jump is being calculated in ALU
  output logic                 branch_in_dec_o,
  
  //
  output logic rf_we
  
    );
    import ibex_pkg::*; 
    logic csr_illegal;
    logic [31:0] instr;
    csr_op_e     csr_op;
    opcode_e     opcode;
    assign instr     = instr_rdata_i;
    logic [4:0] instr_rs1;
    logic [4:0] instr_rd;
    assign instr_rd = instr[11:7];
    assign instr_rs1 = instr[19:15];
    logic illegal_insn;

    
    /////////////
  // Decoder //
  /////////////

  always_comb begin
    jump_in_dec_o         = 1'b0;
    jump_set_o            = 1'b0;
    branch_in_dec_o       = 1'b0;
    icache_inval_o        = 1'b0;

    multdiv_operator_o    = MD_OP_MULL;
    multdiv_signed_mode_o = 2'b00;

    rf_wdata_sel_o        = RF_WD_EX;
    rf_we                 = 1'b0;           ///
    rf_ren_a_o            = 1'b0;
    rf_ren_b_o            = 1'b0;

    csr_access_o          = 1'b0;
    csr_illegal           = 1'b0;
    csr_op                = CSR_OP_READ;

    data_we_o             = 1'b0;
    data_type_o           = 2'b00;
    data_sign_extension_o = 1'b0;
    data_req_o            = 1'b0;

    illegal_insn          = 1'b0;
    ebrk_insn_o           = 1'b0;
    mret_insn_o           = 1'b0;
    dret_insn_o           = 1'b0;
    ecall_insn_o          = 1'b0;
    wfi_insn_o            = 1'b0;

    opcode                = opcode_e'(instr[6:0]);

    unique case (opcode)

      ///////////
      // Jumps //
      ///////////

      OPCODE_JAL: begin   // Jump and Link
        jump_in_dec_o      = 1'b1;

        if (instr_first_cycle_i) begin
          // Calculate jump target (and store PC + 4 if BranchTargetALU is configured)
          rf_we            = BranchTargetALU;
          jump_set_o       = 1'b1;
        end else begin
          // Calculate and store PC+4
          rf_we            = 1'b1;
        end
      end

      OPCODE_JALR: begin  // Jump and Link Register
        jump_in_dec_o      = 1'b1;

        if (instr_first_cycle_i) begin
          // Calculate jump target (and store PC + 4 if BranchTargetALU is configured)
          rf_we            = BranchTargetALU;
          jump_set_o       = 1'b1;
        end else begin
          // Calculate and store PC+4
          rf_we            = 1'b1;
        end
        if (instr[14:12] != 3'b0) begin
          illegal_insn = 1'b1;
        end

        rf_ren_a_o = 1'b1;
      end

      OPCODE_BRANCH: begin // Branch
        branch_in_dec_o       = 1'b1;
        // Check branch condition selection
        unique case (instr[14:12])
          3'b000,
          3'b001,
          3'b100,
          3'b101,
          3'b110,
          3'b111:  illegal_insn = 1'b0;
          default: illegal_insn = 1'b1;
        endcase

        rf_ren_a_o = 1'b1;
        rf_ren_b_o = 1'b1;
      end

      ////////////////
      // Load/store //
      ////////////////

      OPCODE_STORE: begin
        rf_ren_a_o         = 1'b1;
        rf_ren_b_o         = 1'b1;
        data_req_o         = 1'b1;
        data_we_o          = 1'b1;

        if (instr[14]) begin
          illegal_insn = 1'b1;
        end

        // store size
        unique case (instr[13:12])
          2'b00:   data_type_o  = 2'b10; // sb
          2'b01:   data_type_o  = 2'b01; // sh
          2'b10:   data_type_o  = 2'b00; // sw
          default: illegal_insn = 1'b1;
        endcase
      end

      OPCODE_LOAD: begin
        rf_ren_a_o          = 1'b1;
        data_req_o          = 1'b1;
        data_type_o         = 2'b00;

        // sign/zero extension
        data_sign_extension_o = ~instr[14];

        // load size
        unique case (instr[13:12])
          2'b00: data_type_o = 2'b10; // lb(u)
          2'b01: data_type_o = 2'b01; // lh(u)
          2'b10: begin
            data_type_o = 2'b00;      // lw
            if (instr[14]) begin
              illegal_insn = 1'b1;    // lwu does not exist
            end
          end
          default: begin
            illegal_insn = 1'b1;
          end
        endcase
      end

      /////////
      // ALU //
      /////////

      OPCODE_LUI: begin  // Load Upper Immediate
        rf_we            = 1'b1;
      end

      OPCODE_AUIPC: begin  // Add Upper Immediate to PC
        rf_we            = 1'b1;
      end

      OPCODE_OP_IMM: begin // Register-Immediate ALU Operations
        rf_ren_a_o       = 1'b1;
        rf_we            = 1'b1;

        unique case (instr[14:12])
          3'b000,
          3'b010,
          3'b011,
          3'b100,
          3'b110,
          3'b111: illegal_insn = 1'b0;

          3'b001: begin
            unique case (instr[31:27])
              5'b0_0000: illegal_insn = (instr[26:25] == 2'b00) ? 1'b0 : 1'b1;        // slli
              5'b0_0100: begin                                                        // sloi
                illegal_insn = (RV32B == RV32BOTEarlGrey || RV32B == RV32BFull) ? 1'b0 : 1'b1;
              end
              5'b0_1001,                                                              // bclri
              5'b0_0101,                                                              // bseti
              5'b0_1101: illegal_insn = (RV32B != RV32BNone) ? 1'b0 : 1'b1;           // binvi
              5'b0_0001: begin
                if (instr[26] == 1'b0) begin                                          // shfl
                  illegal_insn = (RV32B == RV32BOTEarlGrey || RV32B == RV32BFull) ? 1'b0 : 1'b1;
                end else begin
                  illegal_insn = 1'b1;
                end
              end
              5'b0_1100: begin
                unique case(instr[26:20])
                  7'b000_0000,                                                         // clz
                  7'b000_0001,                                                         // ctz
                  7'b000_0010,                                                         // cpop
                  7'b000_0100,                                                         // sext.b
                  7'b000_0101: illegal_insn = (RV32B != RV32BNone) ? 1'b0 : 1'b1;      // sext.h
                  7'b001_0000,                                                         // crc32.b
                  7'b001_0001,                                                         // crc32.h
                  7'b001_0010,                                                         // crc32.w
                  7'b001_1000,                                                         // crc32c.b
                  7'b001_1001,                                                         // crc32c.h
                  7'b001_1010: begin                                                   // crc32c.w
                    illegal_insn = (RV32B == RV32BOTEarlGrey || RV32B == RV32BFull) ? 1'b0 : 1'b1;
                  end
                  default: illegal_insn = 1'b1;
                endcase
              end
              default : illegal_insn = 1'b1;
            endcase
          end

          3'b101: begin
            if (instr[26]) begin
              illegal_insn = (RV32B != RV32BNone) ? 1'b0 : 1'b1;                       // fsri
            end else begin
              unique case (instr[31:27])
                5'b0_0000,                                                             // srli
                5'b0_1000: illegal_insn = (instr[26:25] == 2'b00) ? 1'b0 : 1'b1;       // srai

                5'b0_0100: begin                                                       // sroi
                  illegal_insn = (RV32B == RV32BOTEarlGrey || RV32B == RV32BFull) ? 1'b0 : 1'b1;
                end
                5'b0_1100,                                                             // rori
                5'b0_1001: illegal_insn = (RV32B != RV32BNone) ? 1'b0 : 1'b1;          // bexti

                5'b0_1101: begin
                  if (RV32B == RV32BOTEarlGrey || RV32B == RV32BFull) begin
                    illegal_insn = 1'b0;                                               // grevi
                  end else if (RV32B == RV32BBalanced) begin
                    illegal_insn = (instr[24:20] == 5'b11000) ? 1'b0 : 1'b1;           // rev8
                  end else begin
                    illegal_insn = 1'b1;
                  end
                end
                5'b0_0101: begin
                  if (RV32B == RV32BOTEarlGrey || RV32B == RV32BFull) begin
                    illegal_insn = 1'b0;                                              // gorci
                  end else if (instr[24:20] == 5'b00111) begin
                    illegal_insn = (RV32B == RV32BBalanced) ? 1'b0 : 1'b1;            // orc.b
                  end else begin
                    illegal_insn = 1'b1;
                  end
                end
                5'b0_0001: begin
                  if (instr[26] == 1'b0) begin                                        // unshfl
                    illegal_insn = (RV32B == RV32BOTEarlGrey || RV32B == RV32BFull) ? 1'b0 : 1'b1;
                  end else begin
                    illegal_insn = 1'b1;
                  end
                end

                default: illegal_insn = 1'b1;
              endcase
            end
          end

          default: illegal_insn = 1'b1;
        endcase
      end

      OPCODE_OP: begin  // Register-Register ALU operation
        rf_ren_a_o      = 1'b1;
        rf_ren_b_o      = 1'b1;
        rf_we           = 1'b1;
        if ({instr[26], instr[13:12]} == {1'b1, 2'b01}) begin
          illegal_insn = (RV32B != RV32BNone) ? 1'b0 : 1'b1; // cmix / cmov / fsl / fsr
        end else begin
          unique case ({instr[31:25], instr[14:12]})
            // RV32I ALU operations
            {7'b000_0000, 3'b000},
            {7'b010_0000, 3'b000},
            {7'b000_0000, 3'b010},
            {7'b000_0000, 3'b011},
            {7'b000_0000, 3'b100},
            {7'b000_0000, 3'b110},
            {7'b000_0000, 3'b111},
            {7'b000_0000, 3'b001},
            {7'b000_0000, 3'b101},
            {7'b010_0000, 3'b101}: illegal_insn = 1'b0;

            // RV32B zba
            {7'b001_0000, 3'b010}, // sh1add
            {7'b001_0000, 3'b100}, // sh2add
            {7'b001_0000, 3'b110}, // sh3add
            // RV32B zbb
            {7'b010_0000, 3'b111}, // andn
            {7'b010_0000, 3'b110}, // orn
            {7'b010_0000, 3'b100}, // xnor
            {7'b011_0000, 3'b001}, // rol
            {7'b011_0000, 3'b101}, // ror
            {7'b000_0101, 3'b100}, // min
            {7'b000_0101, 3'b110}, // max
            {7'b000_0101, 3'b101}, // minu
            {7'b000_0101, 3'b111}, // maxu
            {7'b000_0100, 3'b100}, // pack
            {7'b010_0100, 3'b100}, // packu
            {7'b000_0100, 3'b111}, // packh
            // RV32B zbs
            {7'b010_0100, 3'b001}, // bclr
            {7'b001_0100, 3'b001}, // bset
            {7'b011_0100, 3'b001}, // binv
            {7'b010_0100, 3'b101}, // bext
            // RV32B zbf
            {7'b010_0100, 3'b111}: illegal_insn = (RV32B != RV32BNone) ? 1'b0 : 1'b1; // bfp
            // RV32B zbp
            {7'b011_0100, 3'b101}, // grev
            {7'b001_0100, 3'b101}, // gorc
            {7'b000_0100, 3'b001}, // shfl
            {7'b000_0100, 3'b101}, // unshfl
            {7'b001_0100, 3'b010}, // xperm.n
            {7'b001_0100, 3'b100}, // xperm.b
            {7'b001_0100, 3'b110}, // xperm.h
            {7'b001_0000, 3'b001}, // slo
            {7'b001_0000, 3'b101}, // sro
            // RV32B zbc
            {7'b000_0101, 3'b001}, // clmul
            {7'b000_0101, 3'b010}, // clmulr
            {7'b000_0101, 3'b011}: begin // clmulh
              illegal_insn = (RV32B == RV32BOTEarlGrey || RV32B == RV32BFull) ? 1'b0 : 1'b1;
            end
            // RV32B zbe
            {7'b010_0100, 3'b110}, // bdecompress
            {7'b000_0100, 3'b110}: illegal_insn = (RV32B == RV32BFull) ? 1'b0 : 1'b1; // bcompress

            // RV32M instructions
            {7'b000_0001, 3'b000}: begin // mul
              multdiv_operator_o    = MD_OP_MULL;
              multdiv_signed_mode_o = 2'b00;
              illegal_insn          = (RV32M == RV32MNone) ? 1'b1 : 1'b0;
            end
            {7'b000_0001, 3'b001}: begin // mulh
              multdiv_operator_o    = MD_OP_MULH;
              multdiv_signed_mode_o = 2'b11;
              illegal_insn          = (RV32M == RV32MNone) ? 1'b1 : 1'b0;
            end
            {7'b000_0001, 3'b010}: begin // mulhsu
              multdiv_operator_o    = MD_OP_MULH;
              multdiv_signed_mode_o = 2'b01;
              illegal_insn          = (RV32M == RV32MNone) ? 1'b1 : 1'b0;
            end
            {7'b000_0001, 3'b011}: begin // mulhu
              multdiv_operator_o    = MD_OP_MULH;
              multdiv_signed_mode_o = 2'b00;
              illegal_insn          = (RV32M == RV32MNone) ? 1'b1 : 1'b0;
            end
            {7'b000_0001, 3'b100}: begin // div
              multdiv_operator_o    = MD_OP_DIV;
              multdiv_signed_mode_o = 2'b11;
              illegal_insn          = (RV32M == RV32MNone) ? 1'b1 : 1'b0;
            end
            {7'b000_0001, 3'b101}: begin // divu
              multdiv_operator_o    = MD_OP_DIV;
              multdiv_signed_mode_o = 2'b00;
              illegal_insn          = (RV32M == RV32MNone) ? 1'b1 : 1'b0;
            end
            {7'b000_0001, 3'b110}: begin // rem
              multdiv_operator_o    = MD_OP_REM;
              multdiv_signed_mode_o = 2'b11;
              illegal_insn          = (RV32M == RV32MNone) ? 1'b1 : 1'b0;
            end
            {7'b000_0001, 3'b111}: begin // remu
              multdiv_operator_o    = MD_OP_REM;
              multdiv_signed_mode_o = 2'b00;
              illegal_insn          = (RV32M == RV32MNone) ? 1'b1 : 1'b0;
            end
            default: begin
              illegal_insn = 1'b1;
            end
          endcase
        end
      end

      /////////////
      // Special //
      /////////////

      OPCODE_MISC_MEM: begin
        unique case (instr[14:12])
          3'b000: begin
            // FENCE is treated as a NOP since all memory operations are already strictly ordered.
            rf_we           = 1'b0;
          end
          3'b001: begin
            // FENCE.I is implemented as a jump to the next PC, this gives the required flushing
            // behaviour (iside prefetch buffer flushed and response to any outstanding iside
            // requests will be ignored).
            // If present, the ICache will also be flushed.
            jump_in_dec_o   = 1'b1;

            rf_we           = 1'b0;

            if (instr_first_cycle_i) begin
              jump_set_o       = 1'b1;
              icache_inval_o   = 1'b1;
            end
          end
          default: begin
            illegal_insn       = 1'b1;
          end
        endcase
      end

      OPCODE_SYSTEM: begin
        if (instr[14:12] == 3'b000) begin
          // non CSR related SYSTEM instructions
          unique case (instr[31:20])
            12'h000:  // ECALL
              // environment (system) call
              ecall_insn_o = 1'b1;

            12'h001:  // ebreak
              // debugger trap
              ebrk_insn_o = 1'b1;

            12'h302:  // mret
              mret_insn_o = 1'b1;

            12'h7b2:  // dret
              dret_insn_o = 1'b1;

            12'h105:  // wfi
              wfi_insn_o = 1'b1;

            default:
              illegal_insn = 1'b1;
          endcase

          // rs1 and rd must be 0
          if (instr_rs1 != 5'b0 || instr_rd != 5'b0) begin
            illegal_insn = 1'b1;
          end
        end else begin
          // instruction to read/modify CSR
          csr_access_o     = 1'b1;
          rf_wdata_sel_o   = RF_WD_CSR;
          rf_we            = 1'b1;

          if (~instr[14]) begin
            rf_ren_a_o         = 1'b1;
          end

          unique case (instr[13:12])
            2'b01:   csr_op = CSR_OP_WRITE;
            2'b10:   csr_op = CSR_OP_SET;
            2'b11:   csr_op = CSR_OP_CLEAR;
            default: csr_illegal = 1'b1;
          endcase

          illegal_insn = csr_illegal;
        end

      end
      default: begin
        illegal_insn = 1'b1;
      end
    endcase

    // make sure illegal compressed instructions cause illegal instruction exceptions
    if (illegal_c_insn_i) begin
      illegal_insn = 1'b1;
    end

    // make sure illegal instructions detected in the decoder do not propagate from decoder
    // into register file, LSU, EX, WB, CSRs, PC
    // NOTE: instructions can also be detected to be illegal inside the CSRs (upon accesses with
    // insufficient privileges), or when accessing non-available registers in RV32E,
    // these cases are not handled here
    if (illegal_insn) begin
      rf_we           = 1'b0;
      data_req_o      = 1'b0;
      data_we_o       = 1'b0;
      jump_in_dec_o   = 1'b0;
      jump_set_o      = 1'b0;
      branch_in_dec_o = 1'b0;
      csr_access_o    = 1'b0;
    end
  end
  ///////////////////////
  // CSR operand check //
  ///////////////////////
  always_comb begin : csr_operand_check
    csr_op_o = csr_op;

    // CSRRSI/CSRRCI must not write 0 to CSRs (uimm[4:0]=='0)
    // CSRRS/CSRRC must not write from x0 to CSRs (rs1=='0)
    if ((csr_op == CSR_OP_SET || csr_op == CSR_OP_CLEAR) &&
        instr_rs1 == '0) begin
      csr_op_o = CSR_OP_READ;
    end
  end
  assign illegal_insn_o = illegal_insn;
endmodule
