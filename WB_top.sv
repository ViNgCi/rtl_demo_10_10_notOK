`timescale 1ns / 1ps
//////////////////////////////////////////////////////////////////////////////////
// Company: 
// Engineer: 
// 
// Create Date: 10/07/2024 02:49:09 PM
// Design Name: 
// Module Name: WB_top
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


module WB_top(
    input  logic                     clk_i,
    input  logic                     rst_ni,
    
    input  logic [4:0]               rf_waddr_EX,         // From EX
    input  logic [31:0]              rf_wdata_EX,         // From EX
    input  logic                     rf_we_EX,            // From EX
    
    //input  logic                     en_wb_i,
    input  ibex_pkg::wb_instr_type_e instr_type_wb_i,           // frOM ID/EX
    input  logic [31:0]              pc_EX_i,                   // From ID/EX
    input  logic                     instr_is_compressed_EX_i,  // From ID/EX
    input  logic                     instr_perf_count_id_i,     // From ID/EX
    
    output logic                     perf_instr_ret_wb_o,
    output logic                     perf_instr_ret_compressed_wb_o,
    output logic                     perf_instr_ret_wb_spec_o,
    output logic                     perf_instr_ret_compressed_wb_spec_o,
      
    input  logic [31:0]              rf_wdata_lsu_i,        // From LSU
    input  logic                     rf_we_lsu_i,           // From LSU
    
    input logic                      lsu_resp_valid_i,      // From LSU
    input logic                      lsu_resp_err_i,        // From LSU
    
    output logic [4:0]               rf_waddr_WB_o,
    output logic [31:0]              rf_wdata_WB_o,
    output logic                     rf_we_WB_o,
    
    output logic                     ready_wb_o


    );
    logic [4:0]    rf_waddr_WB_r;
    logic [31:0]   rf_wdata_WB_r;
    logic          rf_we_WB_r;
    logic          wb_done;
    
    ibex_pkg::wb_instr_type_e instr_type_wb_r;           // frOM ID/EX
    logic [31:0]              pc_EX_r;                   // From ID/EX
    logic                     instr_is_compressed_EX_r;  // From ID/EX
    logic                     instr_perf_count_id_r;     // From ID/EX
    assign wb_done = (instr_type_wb_r == WB_INSTR_OTHER) | lsu_resp_valid_i;;
    // EX/WB Pipeline
    always @(posedge clk_i or negedge rst_ni) begin
        if(rst_ni == 1'b0) begin
           rf_waddr_WB_r <=  5'b0;
           rf_wdata_WB_r <=  32'b0;
           rf_we_WB_r    <=  1'b0;
           
           instr_type_wb_r <=wb_instr_type_e'(0);
           pc_EX_r         <='0;
           instr_is_compressed_EX_r <='0;
           instr_perf_count_id_r <='0;
        end else begin
           rf_waddr_WB_r <= rf_waddr_EX;
           rf_wdata_WB_r <= rf_wdata_EX;
           rf_we_WB_r    <= rf_we_EX ;
           
           instr_type_wb_r <= instr_type_wb_i;
           pc_EX_r <=pc_EX_i;
           instr_is_compressed_EX_r <=instr_is_compressed_EX_i;
           instr_perf_count_id_r <=instr_perf_count_id_i;
        end
    end
    
    // 0 == RF write from EX
    // 1 == RF write from LSU
    logic [31:0] rf_wdata_wb_mux[2];
    logic [1:0]  rf_wdata_wb_mux_we;
    
    assign rf_wdata_wb_mux[0] = rf_wdata_WB_r;
    assign rf_wdata_wb_mux[1] = rf_wdata_lsu_i;
    
    assign rf_wdata_wb_mux_we[0] = rf_we_WB_r;      // NOT DONE YET
                                    //& wb_valid_q;
    assign rf_wdata_wb_mux_we[1] = rf_we_lsu_i;     // NOT DONE YET                            
    
    // RF write data can come from ID results (all RF writes that aren't because of loads will come
  // from here) or the LSU (RF writes for load data)
  assign rf_wdata_wb_o = ({32{rf_wdata_wb_mux_we[0]}} & rf_wdata_wb_mux[0]) |
                         ({32{rf_wdata_wb_mux_we[1]}} & rf_wdata_wb_mux[1]);
  assign rf_we_WB_o    = |rf_wdata_wb_mux_we;
  assign rf_waddr_WB_o = rf_waddr_WB_r;
  
  assign ready_WB_o = wb_done;
endmodule
