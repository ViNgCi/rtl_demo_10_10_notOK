//`timescale 1ns / 1ps
//////////////////////////////////////////////////////////////////////////////////
// Company: 
// Engineer: 
// 
// Create Date: 08/23/2024 02:24:33 PM
// Design Name: 
// Module Name: PC
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


module PC import ibex_pkg ::*; #(
  parameter int unsigned DmHaltAddr        = 32'h1A110800,
  parameter int unsigned DmExceptionAddr   = 32'h1A110808
     )
(   
    input  logic [31:0]                  boot_addr_i,
    
    // Input control signal
    input  logic                        pc_set_i,                 // set the PC to a new value
    input  pc_sel_e                     pc_mux_i,                 // selector for PC multiplexer

    input  exc_pc_sel_e                 exc_pc_mux_i,             // selects ISR address
    input  exc_cause_t                  exc_cause,                // selects ISR address for
                                                                // vectorized interrupt lines
    // Branch input
    input logic [31:0]                  predict_branch_pc,
    input logic                         predict_branch_taken,
    input  logic [31:0]                 branch_target_ex_i,       // branch/jump target address
    
    
    // CSRs input 
    input  logic [31:0]                 csr_mepc_i,               // PC to restore after handling
                                                                    // the interrupt/exception
    input  logic [31:0]                 csr_depc_i,               // PC to restore after handling
                                                                    // the debug request
    input  logic [31:0]                 csr_mtvec_i,              // base PC to jump to on exception
    
    // Addr
    output logic [31:0]                 fetch_addr_n,
    output logic                        csr_mtvec_init_o         // tell CS regfile to init mtvec
    
    );
    
    ibex_pkg::pc_sel_e pc_mux_internal;
    logic       [31:0] exc_pc;
    logic        [4:0] irq_vec;
    
    
    
   // exception PC selection mux
  always_comb begin : exc_pc_mux
    irq_vec = exc_cause.lower_cause;

    if (exc_cause.irq_int) begin
      // All internal interrupts go to the NMI vector
      irq_vec = ExcCauseIrqNm.lower_cause;
    end

    unique case (exc_pc_mux_i)
      EXC_PC_EXC:     exc_pc = { csr_mtvec_i[31:8], 8'h00                };
      EXC_PC_IRQ:     exc_pc = { csr_mtvec_i[31:8], 1'b0, irq_vec, 2'b00 };
      EXC_PC_DBD:     exc_pc = DmHaltAddr;
      EXC_PC_DBG_EXC: exc_pc = DmExceptionAddr;
      default:        exc_pc = { csr_mtvec_i[31:8], 8'h00                };
    endcase
  end

  // The Branch predictor can provide a new PC which is internal to if_stage. Only override the mux
  // select to choose this if the core isn't already trying to set a PC.
  assign pc_mux_internal = (predict_branch_taken && !pc_set_i) ? PC_BP : pc_mux_i;

  // fetch address selection mux
  always_comb begin : fetch_addr_mux
    unique case (pc_mux_internal)
      PC_BOOT: fetch_addr_n = { boot_addr_i[31:8], 8'h80 };
      PC_JUMP: fetch_addr_n = branch_target_ex_i;
      PC_EXC:  fetch_addr_n = exc_pc;                       // set PC to exception handler
      PC_ERET: fetch_addr_n = csr_mepc_i;                   // restore PC when returning from EXC
      PC_DRET: fetch_addr_n = csr_depc_i;
      // Without branch predictor will never get pc_mux_internal == PC_BP. We still handle no branch
      // predictor case here to ensure redundant mux logic isn't synthesised.
      PC_BP:   fetch_addr_n =  predict_branch_pc ;
      default: fetch_addr_n = { boot_addr_i[31:8], 8'h80 };
    endcase
  end
  assign csr_mtvec_init_o = (pc_mux_i == PC_BOOT) & pc_set_i;
endmodule
