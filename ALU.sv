//`timescale 1ns / 1ps
//////////////////////////////////////////////////////////////////////////////////
// Company: 
// Engineer: 
// 
// Create Date: 08/16/2024 05:18:58 PM
// Design Name: 
// Module Name: ALU
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


module ALU(
  input  ibex_pkg::alu_op_e operator_i,
  input  logic [31:0]       operand_a_i,
  input  logic [31:0]       operand_b_i,

  input  logic              instr_first_cycle_i,

  input  logic [32:0]       multdiv_operand_a_i,    // from MUL/DIV
  input  logic [32:0]       multdiv_operand_b_i,    // from MUL/DIV

  input  logic              multdiv_sel_i,          

  input  logic [31:0]       imd_val_q_i[2],
  
  output logic [31:0]       imd_val_d_o[2],
  output logic [1:0]        imd_val_we_o,

  output logic [31:0]       adder_result_o,
  output logic [33:0]       adder_result_ext_o,

  output logic [31:0]       result_o,
  output logic              comparison_result_o,
  output logic              is_equal_result_o   
);
import ibex_pkg::*;

  logic [31:0] operand_a_rev;
  logic [32:0] operand_b_neg;

  // bit reverse operand_a for left shifts and bit counting
  for (genvar k = 0; k < 32; k++) begin : gen_rev_operand_a
    assign operand_a_rev[k] = operand_a_i[31-k];
  end
  
  ///////////
  // Adder //
  ///////////

  logic        adder_op_a_shift1;
  logic        adder_op_a_shift2;
  logic        adder_op_a_shift3;
  logic        adder_op_b_negate;
  logic [32:0] adder_in_a, adder_in_b;
  logic [31:0] adder_result;

  always_comb begin
    adder_op_a_shift1 = 1'b0;
    adder_op_a_shift2 = 1'b0;
    adder_op_a_shift3 = 1'b0;
    adder_op_b_negate = 1'b0;
    unique case (operator_i)
      // Adder OPs
      ALU_SUB,

      // Comparator OPs
      ALU_EQ,   ALU_NE,
      ALU_GE,   ALU_GEU,
      ALU_LT,   ALU_LTU,
      ALU_SLT,  ALU_SLTU,

      // MinMax OPs (RV32B Ops)
      ALU_MIN,  ALU_MINU,
      ALU_MAX,  ALU_MAXU: adder_op_b_negate = 1'b1;

      // Address Calculation OPs (RV32B Ops)
      ALU_SH1ADD: adder_op_a_shift1 = 1'b1;
      ALU_SH2ADD: adder_op_a_shift2 = 1'b1;
      ALU_SH3ADD: adder_op_a_shift3 = 1'b1;

      default:;
    endcase
  end

  // prepare operand a
  always_comb begin
    unique case (1'b1)
      multdiv_sel_i:     adder_in_a = multdiv_operand_a_i;
      adder_op_a_shift1: adder_in_a = {operand_a_i[30:0],2'b01};
      adder_op_a_shift2: adder_in_a = {operand_a_i[29:0],3'b001};
      adder_op_a_shift3: adder_in_a = {operand_a_i[28:0],4'b0001};
      default:           adder_in_a = {operand_a_i,1'b1};
    endcase
  end

  // prepare operand b
  assign operand_b_neg = {operand_b_i,1'b0} ^ {33{1'b1}};
  always_comb begin
    unique case (1'b1)
      multdiv_sel_i:     adder_in_b = multdiv_operand_b_i;
      adder_op_b_negate: adder_in_b = operand_b_neg;
      default:           adder_in_b = {operand_b_i, 1'b0};
    endcase
  end

  // actual adder
  assign adder_result_ext_o = $unsigned(adder_in_a) + $unsigned(adder_in_b);

  assign adder_result       = adder_result_ext_o[32:1];

  assign adder_result_o     = adder_result;
  
  
  ////////////////
  // Comparison //
  ////////////////

  logic is_equal;
  logic is_greater_equal;  // handles both signed and unsigned forms
  logic cmp_signed;

  always_comb begin
    unique case (operator_i)
      ALU_GE,
      ALU_LT,
      ALU_SLT,
      // RV32B only
      ALU_MIN,
      ALU_MAX: cmp_signed = 1'b1;

      default: cmp_signed = 1'b0;
    endcase
  end

  assign is_equal = (adder_result == 32'b0);
  assign is_equal_result_o = is_equal;

  // Is greater equal
  always_comb begin
    if ((operand_a_i[31] ^ operand_b_i[31]) == 1'b0) begin
      is_greater_equal = (adder_result[31] == 1'b0);
    end else begin
      is_greater_equal = operand_a_i[31] ^ (cmp_signed);
    end
  end
   // generate comparison result
  logic cmp_result;

  always_comb begin
    unique case (operator_i)
      ALU_EQ:             cmp_result =  is_equal;
      ALU_NE:             cmp_result = ~is_equal;
      ALU_GE,   ALU_GEU,
      ALU_MAX,  ALU_MAXU: cmp_result = is_greater_equal; // RV32B only
      ALU_LT,   ALU_LTU,
      ALU_MIN,  ALU_MINU, //RV32B only
      ALU_SLT,  ALU_SLTU: cmp_result = ~is_greater_equal;

      default: cmp_result = is_equal;
    endcase
  end

  assign comparison_result_o = cmp_result;
  
  ///////////
  // Shift //
  ///////////
  logic       shift_left;
  logic       shift_ones;
  logic       shift_arith;
  logic       shift_funnel;
  logic       shift_sbmode;
  logic [5:0] shift_amt;
  logic [5:0] shift_amt_compl; // complementary shift amount (32 - shift_amt)

  logic        [31:0] shift_operand;
  logic signed [32:0] shift_result_ext_signed;
  logic        [32:0] shift_result_ext;
  logic               unused_shift_result_ext;
  logic        [31:0] shift_result;
  logic        [31:0] shift_result_rev;

  // zbf
  logic bfp_op;
  logic [4:0]  bfp_len;
  logic [4:0]  bfp_off;
  logic [31:0] bfp_mask;
  logic [31:0] bfp_mask_rev;
  logic [31:0] bfp_result;

  // bfp: shares the shifter structure to compute bfp_mask << bfp_off
  assign bfp_op =  (operator_i == ALU_BFP);
  assign bfp_len = {~(|operand_b_i[27:24]), operand_b_i[27:24]}; // len = 0 encodes for len = 16
  assign bfp_off = operand_b_i[20:16];
  assign bfp_mask =  ~(32'hffff_ffff << bfp_len) ;
  for (genvar i = 0; i < 32; i++) begin : gen_rev_bfp_mask
    assign bfp_mask_rev[i] = bfp_mask[31-i];
  end

  assign bfp_result = (~shift_result & operand_a_i) | ((operand_b_i & bfp_mask) << bfp_off);

  // bit shift_amt[5]: word swap bit: only considered for FSL/FSR.
  // if set, reverse operations in first and second cycle.
  assign shift_amt[5] = operand_b_i[5] & shift_funnel;
  assign shift_amt_compl = 32 - operand_b_i[4:0];

  always_comb begin
    if (bfp_op) begin
      shift_amt[4:0] = bfp_off;  // length field of bfp control word
    end else begin
      shift_amt[4:0] = instr_first_cycle_i ?
          (operand_b_i[5] && shift_funnel ? shift_amt_compl[4:0] : operand_b_i[4:0]) :
          (operand_b_i[5] && shift_funnel ? operand_b_i[4:0] : shift_amt_compl[4:0]);
    end
  end

  // single-bit mode: shift
  assign shift_sbmode = (operator_i == ALU_BSET) | (operator_i == ALU_BCLR) | (operator_i == ALU_BINV) ;

  // left shift if this is:
  // * a standard left shift (slo, sll)
  // * a rol in the first cycle
  // * a ror in the second cycle
  // * fsl: without word-swap bit: first cycle, else: second cycle
  // * fsr: without word-swap bit: second cycle, else: first cycle
  // * a single-bit instruction: bclr, bset, binv (excluding bext)
  // * bfp: bfp_mask << bfp_off
  always_comb begin
    unique case (operator_i)
      ALU_SLL: shift_left = 1'b1;
      ALU_SLO: shift_left = 1'b0;
      ALU_BFP: shift_left = 1'b1 ;
      ALU_ROL: shift_left = instr_first_cycle_i ;
      ALU_ROR: shift_left = ~instr_first_cycle_i ;
      ALU_FSL: shift_left = (shift_amt[5] ? ~instr_first_cycle_i : instr_first_cycle_i);
      ALU_FSR: shift_left = (shift_amt[5] ? instr_first_cycle_i : ~instr_first_cycle_i);
      default: shift_left = 1'b0;
    endcase
    if (shift_sbmode) begin
      shift_left = 1'b1;
    end
  end

  assign shift_arith  = (operator_i == ALU_SRA);
  assign shift_ones   = 1'b0;
  assign shift_funnel =  1'b0;

  // shifter structure.
  always_comb begin
    // select shifter input
    // for bfp, sbmode and shift_left the corresponding bit-reversed input is chosen.
      unique case (1'b1)
        bfp_op:       shift_operand = bfp_mask_rev;
        shift_sbmode: shift_operand = 32'h8000_0000;
        default:      shift_operand = shift_left ? operand_a_rev : operand_a_i;
      endcase
    

    shift_result_ext_signed =
        $signed({shift_ones | (shift_arith & shift_operand[31]), shift_operand}) >>> shift_amt[4:0];
    shift_result_ext = $unsigned(shift_result_ext_signed);

    shift_result            = shift_result_ext[31:0];
    unused_shift_result_ext = shift_result_ext[32];

    for (int unsigned i = 0; i < 32; i++) begin
      shift_result_rev[i] = shift_result[31-i];
    end

    shift_result = shift_left ? shift_result_rev : shift_result;

  end
  
  ///////////////////
  // Bitwise Logic //
  ///////////////////

  logic bwlogic_or;
  logic bwlogic_and;
  logic [31:0] bwlogic_operand_b;
  logic [31:0] bwlogic_or_result;
  logic [31:0] bwlogic_and_result;
  logic [31:0] bwlogic_xor_result;
  logic [31:0] bwlogic_result;

  logic bwlogic_op_b_negate;

  always_comb begin
    unique case (operator_i)
      // Logic-with-negate OPs (RV32B Ops)
      ALU_XNOR,
      ALU_ORN,
      ALU_ANDN: bwlogic_op_b_negate = 1'b1 ;
      ALU_CMIX: bwlogic_op_b_negate =  ~instr_first_cycle_i ;
      default:  bwlogic_op_b_negate = 1'b0;
    endcase
  end

  assign bwlogic_operand_b = bwlogic_op_b_negate ? operand_b_neg[32:1] : operand_b_i;

  assign bwlogic_or_result  = operand_a_i | bwlogic_operand_b;
  assign bwlogic_and_result = operand_a_i & bwlogic_operand_b;
  assign bwlogic_xor_result = operand_a_i ^ bwlogic_operand_b;

  assign bwlogic_or  = (operator_i == ALU_OR)  | (operator_i == ALU_ORN);
  assign bwlogic_and = (operator_i == ALU_AND) | (operator_i == ALU_ANDN);

  always_comb begin
    unique case (1'b1)
      bwlogic_or:  bwlogic_result = bwlogic_or_result;
      bwlogic_and: bwlogic_result = bwlogic_and_result;
      default:     bwlogic_result = bwlogic_xor_result;
    endcase
  end

  logic [5:0]  bitcnt_result;
  logic [31:0] minmax_result;
  logic [31:0] pack_result;
  logic [31:0] sext_result;
  logic [31:0] singlebit_result;
  logic [31:0] rev_result;
  logic [31:0] shuffle_result;
  logic [31:0] xperm_result;
  logic [31:0] butterfly_result;
  logic [31:0] invbutterfly_result;
  logic [31:0] clmul_result;
  logic [31:0] multicycle_result;
  
    /////////////////
    // Bitcounting //
    /////////////////

    // The bit-counter structure computes the number of set bits in its operand. Partial results
    // (from left to right) are needed to compute the control masks for computation of
    // bcompress/bdecompress by the butterfly network, if implemented.
    // For cpop, clz and ctz, only the end result is used.

    logic        zbe_op;
    logic        bitcnt_ctz;
    logic        bitcnt_clz;
    logic        bitcnt_cz;
    logic [31:0] bitcnt_bits;
    logic [31:0] bitcnt_mask_op;
    logic [31:0] bitcnt_bit_mask;
    logic [ 5:0] bitcnt_partial [32];
    logic [31:0] bitcnt_partial_lsb_d;
    logic [31:0] bitcnt_partial_msb_d;


    assign bitcnt_ctz    = operator_i == ALU_CTZ;
    assign bitcnt_clz    = operator_i == ALU_CLZ;
    assign bitcnt_cz     = bitcnt_ctz | bitcnt_clz;
    assign bitcnt_result = bitcnt_partial[31];

    // Bit-mask generation for clz and ctz:
    // The bit mask is generated by spreading the lowest-order set bit in the operand to all
    // higher order bits. The resulting mask is inverted to cover the lowest order zeros. In order
    // to create the bit mask for leading zeros, the input operand needs to be reversed.
    assign bitcnt_mask_op = bitcnt_clz ? operand_a_rev : operand_a_i;

    always_comb begin
      bitcnt_bit_mask = bitcnt_mask_op;
      bitcnt_bit_mask |= bitcnt_bit_mask << 1;
      bitcnt_bit_mask |= bitcnt_bit_mask << 2;
      bitcnt_bit_mask |= bitcnt_bit_mask << 4;
      bitcnt_bit_mask |= bitcnt_bit_mask << 8;
      bitcnt_bit_mask |= bitcnt_bit_mask << 16;
      bitcnt_bit_mask = ~bitcnt_bit_mask;
    end

    assign zbe_op = (operator_i == ALU_BCOMPRESS) | (operator_i == ALU_BDECOMPRESS);

    always_comb begin
      unique case (1'b1)
        zbe_op:      bitcnt_bits = operand_b_i;
        bitcnt_cz:   bitcnt_bits = bitcnt_bit_mask & ~bitcnt_mask_op; // clz / ctz
        default:     bitcnt_bits = operand_a_i; // cpop
      endcase
    end

    always_comb begin
      bitcnt_partial = '{default: '0};
      // stage 1
      for (int unsigned i = 1; i < 32; i += 2) begin
        bitcnt_partial[i] = {5'h0, bitcnt_bits[i]} + {5'h0, bitcnt_bits[i-1]};
      end
      // stage 2
      for (int unsigned i = 3; i < 32; i += 4) begin
        bitcnt_partial[i] = bitcnt_partial[i-2] + bitcnt_partial[i];
      end
      // stage 3
      for (int unsigned i = 7; i < 32; i += 8) begin
        bitcnt_partial[i] = bitcnt_partial[i-4] + bitcnt_partial[i];
      end
      // stage 4
      for (int unsigned i = 15; i < 32; i += 16) begin
        bitcnt_partial[i] = bitcnt_partial[i-8] + bitcnt_partial[i];
      end
      // stage 5
      bitcnt_partial[31] = bitcnt_partial[15] + bitcnt_partial[31];
      // ^- primary adder tree
      // -------------------------------
      // ,-intermediate value adder tree
      bitcnt_partial[23] = bitcnt_partial[15] + bitcnt_partial[23];

      // stage 6
      for (int unsigned i = 11; i < 32; i += 8) begin
        bitcnt_partial[i] = bitcnt_partial[i-4] + bitcnt_partial[i];
      end

      // stage 7
      for (int unsigned i = 5; i < 32; i += 4) begin
        bitcnt_partial[i] = bitcnt_partial[i-2] + bitcnt_partial[i];
      end
      // stage 8
      bitcnt_partial[0] = {5'h0, bitcnt_bits[0]};
      for (int unsigned i = 2; i < 32; i += 2) begin
        bitcnt_partial[i] = bitcnt_partial[i-1] + {5'h0, bitcnt_bits[i]};
      end
    end

    ///////////////
    // Min / Max //
    ///////////////

    assign minmax_result = cmp_result ? operand_a_i : operand_b_i;

    //////////
    // Pack //
    //////////

    logic packu;
    logic packh;
    assign packu = operator_i == ALU_PACKU;
    assign packh = operator_i == ALU_PACKH;

    always_comb begin
      unique case (1'b1)
        packu:   pack_result = {operand_b_i[31:16], operand_a_i[31:16]};
        packh:   pack_result = {16'h0, operand_b_i[7:0], operand_a_i[7:0]};
        default: pack_result = {operand_b_i[15:0], operand_a_i[15:0]};
      endcase
    end

    //////////
    // Sext //
    //////////

    assign sext_result = (operator_i == ALU_SEXTB) ?
        { {24{operand_a_i[7]}}, operand_a_i[7:0]} : { {16{operand_a_i[15]}}, operand_a_i[15:0]};

    /////////////////////////////
    // Single-bit Instructions //
    /////////////////////////////

    always_comb begin
      unique case (operator_i)
        ALU_BSET: singlebit_result = operand_a_i | shift_result;
        ALU_BCLR: singlebit_result = operand_a_i & ~shift_result;
        ALU_BINV: singlebit_result = operand_a_i ^ shift_result;
        default:  singlebit_result = {31'h0, shift_result[0]}; // ALU_BEXT
      endcase
    end

    ////////////////////////////////////
    // General Reverse and Or-combine //
    ////////////////////////////////////

    // Only a subset of the general reverse and or-combine instructions are implemented in the
    // balanced version of the B extension. Currently rev8 (shift_amt = 5'b11000) and orc.b
    // (shift_amt = 5'b00111) are supported in the base extension.

    logic [4:0] zbp_shift_amt;
    logic gorc_op;

    assign gorc_op = (operator_i == ALU_GORC);
    assign zbp_shift_amt[2:0] = {3{shift_amt[0]}};
    assign zbp_shift_amt[4:3] = {2{shift_amt[3]}};

    always_comb begin
      rev_result = operand_a_i;

      if (zbp_shift_amt[0]) begin
        rev_result = (gorc_op ? rev_result : 32'h0)       |
                     ((rev_result & 32'h5555_5555) <<  1) |
                     ((rev_result & 32'haaaa_aaaa) >>  1);
      end

      if (zbp_shift_amt[1]) begin
        rev_result = (gorc_op ? rev_result : 32'h0)       |
                     ((rev_result & 32'h3333_3333) <<  2) |
                     ((rev_result & 32'hcccc_cccc) >>  2);
      end

      if (zbp_shift_amt[2]) begin
        rev_result = (gorc_op ? rev_result : 32'h0)       |
                     ((rev_result & 32'h0f0f_0f0f) <<  4) |
                     ((rev_result & 32'hf0f0_f0f0) >>  4);
      end

      if (zbp_shift_amt[3]) begin
        rev_result = (32'h0) |
                     ((rev_result & 32'h00ff_00ff) <<  8) |
                     ((rev_result & 32'hff00_ff00) >>  8);
      end

      if (zbp_shift_amt[4]) begin
        rev_result = (32'h0) |
                     ((rev_result & 32'h0000_ffff) << 16) |
                     ((rev_result & 32'hffff_0000) >> 16);
      end
    end

    logic crc_hmode;
    logic crc_bmode;
    logic [31:0] clmul_result_rev;
    
    // gen_alu_rvb_not_otearlgrey_full
      assign shuffle_result       = '0;
      assign xperm_result         = '0;
      assign clmul_result         = '0;
      // support signals
      assign clmul_result_rev     = '0;
      assign crc_bmode            = '0;
      assign crc_hmode            = '0;
    
    //gen_alu_rvb_not_full
      logic [31:0] unused_imd_val_q_1;
      assign unused_imd_val_q_1   = imd_val_q_i[1];
      assign butterfly_result     = '0;
      assign invbutterfly_result  = '0;
      // support signals
      assign bitcnt_partial_lsb_d = '0;
      assign bitcnt_partial_msb_d = '0;
    //////////////////////////////////////
    // Multicycle Bitmanip Instructions //
    //////////////////////////////////////
    // Ternary instructions + Shift Rotations + Bit Compress/Decompress + CRC
    // For ternary instructions (zbt), operand_a_i is tied to rs1 in the first cycle and rs3 in the
    // second cycle. operand_b_i is always tied to rs2.

    always_comb begin
      unique case (operator_i)
        ALU_CMOV: begin
          multicycle_result = (operand_b_i == 32'h0) ? operand_a_i : imd_val_q_i[0];
          imd_val_d_o = '{operand_a_i, 32'h0};
          if (instr_first_cycle_i) begin
            imd_val_we_o = 2'b01;
          end else begin
            imd_val_we_o = 2'b00;
          end
        end

        ALU_CMIX: begin
          multicycle_result = imd_val_q_i[0] | bwlogic_and_result;
          imd_val_d_o = '{bwlogic_and_result, 32'h0};
          if (instr_first_cycle_i) begin
            imd_val_we_o = 2'b01;
          end else begin
            imd_val_we_o = 2'b00;
          end
        end

        ALU_FSR, ALU_FSL,
        ALU_ROL, ALU_ROR: begin
          if (shift_amt[4:0] == 5'h0) begin
            multicycle_result = shift_amt[5] ? operand_a_i : imd_val_q_i[0];
          end else begin
            multicycle_result = imd_val_q_i[0] | shift_result;
          end
          imd_val_d_o = '{shift_result, 32'h0};
          if (instr_first_cycle_i) begin
            imd_val_we_o = 2'b01;
          end else begin
            imd_val_we_o = 2'b00;
          end
        end

        ALU_CRC32_W, ALU_CRC32C_W,
        ALU_CRC32_H, ALU_CRC32C_H,
        ALU_CRC32_B, ALU_CRC32C_B: begin
            imd_val_d_o = '{operand_a_i, 32'h0};
            imd_val_we_o = 2'b00;
            multicycle_result = '0;
        end

        ALU_BCOMPRESS, ALU_BDECOMPRESS: begin
            imd_val_d_o = '{operand_a_i, 32'h0};
            imd_val_we_o = 2'b00;
            multicycle_result = '0;
        end

        default: begin
          imd_val_d_o = '{operand_a_i, 32'h0};
          imd_val_we_o = 2'b00;
          multicycle_result = '0;
        end
      endcase
    end
    
   ////////////////
  // Result mux //
  ////////////////

  always_comb begin
    result_o   = '0;

    unique case (operator_i)
      // Bitwise Logic Operations (negate: RV32B)
      ALU_XOR,  ALU_XNOR,
      ALU_OR,   ALU_ORN,
      ALU_AND,  ALU_ANDN: result_o = bwlogic_result;

      // Adder Operations
      ALU_ADD,  ALU_SUB,
      // RV32B
      ALU_SH1ADD, ALU_SH2ADD,
      ALU_SH3ADD: result_o = adder_result;

      // Shift Operations
      ALU_SLL,  ALU_SRL,
      ALU_SRA,
      // RV32B
      ALU_SLO,  ALU_SRO: result_o = shift_result;

      // Shuffle Operations (RV32B)
      ALU_SHFL, ALU_UNSHFL: result_o = shuffle_result;

      // Crossbar Permutation Operations (RV32B)
      ALU_XPERM_N, ALU_XPERM_B, ALU_XPERM_H: result_o = xperm_result;

      // Comparison Operations
      ALU_EQ,   ALU_NE,
      ALU_GE,   ALU_GEU,
      ALU_LT,   ALU_LTU,
      ALU_SLT,  ALU_SLTU: result_o = {31'h0,cmp_result};

      // MinMax Operations (RV32B)
      ALU_MIN,  ALU_MAX,
      ALU_MINU, ALU_MAXU: result_o = minmax_result;

      // Bitcount Operations (RV32B)
      ALU_CLZ, ALU_CTZ,
      ALU_CPOP: result_o = {26'h0, bitcnt_result};

      // Pack Operations (RV32B)
      ALU_PACK, ALU_PACKH,
      ALU_PACKU: result_o = pack_result;

      // Sign-Extend (RV32B)
      ALU_SEXTB, ALU_SEXTH: result_o = sext_result;

      // Ternary Bitmanip Operations (RV32B)
      ALU_CMIX, ALU_CMOV,
      ALU_FSL,  ALU_FSR,
      // Rotate Shift (RV32B)
      ALU_ROL, ALU_ROR,
      // Cyclic Redundancy Checks (RV32B)
      ALU_CRC32_W, ALU_CRC32C_W,
      ALU_CRC32_H, ALU_CRC32C_H,
      ALU_CRC32_B, ALU_CRC32C_B,
      // Bit Compress / Decompress (RV32B)
      ALU_BCOMPRESS, ALU_BDECOMPRESS: result_o = multicycle_result;

      // Single-Bit Bitmanip Operations (RV32B)
      ALU_BSET, ALU_BCLR,
      ALU_BINV, ALU_BEXT: result_o = singlebit_result;

      // General Reverse / Or-combine (RV32B)
      ALU_GREV, ALU_GORC: result_o = rev_result;

      // Bit Field Place (RV32B)
      ALU_BFP: result_o = bfp_result;

      // Carry-less Multiply Operations (RV32B)
      ALU_CLMUL, ALU_CLMULR,
      ALU_CLMULH: result_o = clmul_result;

      default: ;
    endcase
  end

  logic unused_shift_amt_compl;
  assign unused_shift_amt_compl = shift_amt_compl[5];
  
endmodule
