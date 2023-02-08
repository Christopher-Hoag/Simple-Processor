`timescale 1ns / 1ps

module Final(
    input clk_i,
    output [7:0] disp_seg_o,
    output [7:0] disp_an_o);
    
    wire clk_multiplex, clock_slow;
    wire [63:0] pass;
    wire [7:0] seg_val [0:7];
    
    wire zero_flag;
    wire [15:0] R_data, W_data;
    wire [7:0] PC_addr, D_addr, RF_W_data, mem_addr;
    wire [3:0] W_addr, Rp_addr, Rq_addr;
    wire [2:0] ALU_sel;
    wire [1:0] mux_sel;
    wire W_wr, Rp_rd, Rq_rd, D_addr_sel, D_rd, D_wr;
    
    disp_7seg     disp1(.Parray (pass),
                        .clk (clk_multiplex), 
                        .CA (disp_seg_o), .AN (disp_an_o));
    clk_divider    clk1(.clk (clk_i),
                        .clk_slow (clock_slow), .clk_multiplex (clk_multiplex));
    Control_Unit    CU1(.clk (clk_i), .zero_flag (zero_flag), .R_data (R_data), .PC_addr (PC_addr), .D_addr (D_addr),
                        .RF_W_data (RF_W_data), .W_addr (W_addr), .Rp_addr (Rp_addr), .Rq_addr (Rq_addr), .ALU_sel (ALU_sel),
                        .mux_sel (mux_sel), .W_wr (W_wr), .Rp_rd (Rp_rd), .Rq_rd (Rq_rd), .D_addr_sel (D_addr_sel), .D_rd (D_rd), .D_wr (D_wr));
    Datapath        DP1(.clk (clk_i), .R_data (R_data), .RF_W_data (RF_W_data), .W_addr (W_addr), .Rp_addr (Rp_addr), .Rq_addr (Rq_addr),
                        .ALU_sel (ALU_sel), .mux_sel (mux_sel), .W_wr (W_wr), .Rp_rd (Rp_rd), .Rq_rd (Rq_rd), .W_data (W_data), .zero_flag (zero_flag));
    memory         Mem1(.clk (clk_i), .rd (D_rd), .wr (D_wr), .addr (mem_addr), .W_data (W_data), .R_data (R_data));
    mux #(.bits(8)) mx1(.i1 (PC_addr), .i2 (D_addr), .i3 (0), .i4 (0), .sel ({0,D_addr_sel}), .out (mem_addr));
                         
    digit_set D1 (4'hA, 1'b0, seg_val[0]);
    digit_set D2 (4'hB, 1'b0, seg_val[1]);
    digit_set D3 (4'hC, 1'b0, seg_val[2]);
    digit_set D4 (4'hD, 1'b0, seg_val[3]);
    digit_set D5 (4'hE, 1'b0, seg_val[4]);
    digit_set D6 (4'hF, 1'b0, seg_val[5]);
    digit_set D7 (4'h1, 1'b0, seg_val[6]);
    digit_set D8 (4'h2, 1'b0, seg_val[7]);
    
    assign pass = {seg_val[0], seg_val[1], seg_val[2], seg_val[3], seg_val[4], seg_val[5], seg_val[6], seg_val[7]};
endmodule

module Control_Unit(
    input clk, zero_flag,
    input [15:0] R_data,
    output [7:0] PC_addr, D_addr, RF_W_data,
    output [3:0] W_addr, Rp_addr, Rq_addr,
    output [2:0] ALU_sel,
    output [1:0] mux_sel,
    output W_wr, Rp_rd, Rq_rd, D_addr_sel, D_rd, D_wr);
    
    wire [15:0] IR_out, IR_d;
    wire [7:0] IR_PC;
    wire PC_ld, PC_clr, PC_inc, IR_ld;
    
    controller              C1(.clk (clk), .zero_flag (zero_flag), .IR_d (IR_d),
                               .D_addr (D_addr), .RF_W_data (RF_W_data), .W_addr (W_addr), .Rp_addr (Rp_addr), .Rq_addr(Rq_addr),
                               .ALU_sel(ALU_sel), .RF_sel(mux_sel), .D_rd(D_rd), .D_wr(D_wr), .W_wr(W_wr), .Rp_rd(Rp_rd), .Rq_rd(Rq_rd),
                               .IR_ld(IR_ld), .D_addr_sel(D_addr_sel), .PC_inc(PC_inc), .PC_clr(PC_clr), .PC_ld (PC_ld));
    Instruction_Register   IR1(.clk (clk), .ld (IR_ld), .R_data (R_data),
                               .out (IR_d));
    Program_Counter        PC1(.clk (clk), .PC_inc (PC_inc), .PC_clr (PC_clr), .PC_ld (PC_ld), .data_in (IR_PC),
                               .count (PC_addr));
    
    assign IR_PC = PC_addr + IR_out[7:0] - 1;

endmodule

module Datapath(
    input clk,
    input [15:0] R_data,
    input [7:0] RF_W_data,
    input [3:0] W_addr, Rp_addr, Rq_addr,
    input [2:0] ALU_sel,
    input [1:0] mux_sel,
    input W_wr, Rp_rd, Rq_rd,
    output [15:0] W_data,
    output reg zero_flag);
    
    wire [15:0] ALU_out, W_temp_data, Rp_data, Rq_data;
    
    mux #(.bits(16)) M1(.i1 (ALU_out), .i2 (R_data), .i3 (RF_W_data), .i4 (0), .sel (mux_sel),
                        .out (W_temp_data));
    ALU              A1(.A (Rp_data), .B (Rq_data), .alu_s (ALU_sel),
                        .C (ALU_out));
    RF               R1(.clk (clk), .W_wr (W_wr), .Rp_rd (Rp_rd), .Rq_rd (Rq_rd),
                        .W_addr (W_addr), .Rp_addr (Rp_addr), .Rq_addr (Rq_addr), .W_data (W_temp_data),
                        .Rp_data (Rp_data), .Rq_data (Rq_data));
    assign W_data = Rp_data;
    
    always @(posedge clk) begin
        if(~|Rp_data)
            zero_flag <= 1;
        else
            zero_flag <= 0;
    end
endmodule

module clk_divider(
    input clk,
    output reg clk_slow, clk_multiplex);
    
    reg[31:0] counter1, counter2;
        initial begin
            counter1      <= 32'h00000000;
            counter2      <= 32'h00000000;
            clk_slow      <= 1'b0;
            clk_multiplex <= 1'b0;
        end
        
    always @(posedge clk) begin
        counter1 <= counter1 + 1;
        counter2 <= counter2 + 1;
        
        if (counter1 >  100000000) begin // ~ 1 second clock
            counter1 <= 32'h00000000;
            clk_slow <= !clk_slow;
        end
        
        if (counter2      >  10000) begin // clock for multiplexing display
            counter2      <= 32'h00000000;
            clk_multiplex <= !clk_multiplex;
        end
    end
endmodule

module digit_set( 
    input [3:0] Value,
    input Decimal_Point,
    output reg [7:0] SS);
    
    always @* begin
        case (Value) 
             4'h0: SS[6:0]  = ~(7'b0111111); 
             4'h1: SS[6:0]  = ~(7'b0000110);
             4'h2: SS[6:0]  = ~(7'b1011011);   
             4'h3: SS[6:0]  = ~(7'b1001111);   
             4'h4: SS[6:0]  = ~(7'b1100110);   
             4'h5: SS[6:0]  = ~(7'b1101101);   
             4'h6: SS[6:0]  = ~(7'b1111101);   
             4'h7: SS[6:0]  = ~(7'b0000111);   
             4'h8: SS[6:0]  = ~(7'b1111111);   
             4'h9: SS[6:0]  = ~(7'b1100111);
             4'hA: SS[6:0]  = ~(7'b1110111);
             4'hB: SS[6:0]  = ~(7'b1111100);
             4'hC: SS[6:0]  = ~(7'b0111001);
             4'hD: SS[6:0]  = ~(7'b1011110);
             4'hE: SS[6:0]  = ~(7'b1111001);
             4'hF: SS[6:0]  = ~(7'b1110001);
          default:  SS[6:0] = ~(7'b1001001);
        endcase
    SS[7] = ~Decimal_Point;   
    end
endmodule

module disp_7seg (
    input [63:0] Parray,
    input  clk,
    output reg [7:0] CA,
    output reg [7:0] AN);
    
    wire [7:0] Cath [0:7]; //[0] is rightmost
    reg [3:0] i;

    assign {Cath [0],Cath [1],Cath [2],Cath [3],Cath [4],Cath [5],Cath [6],Cath [7]} = Parray;
    
    initial begin
        i=4'b0000;
    end
    
    always @(posedge clk) begin
       case (i)   
           4'h0: begin
               AN = ~(8'b00000000);  //All off   
               CA = Cath [0];        //Set cathodes
           end
           4'h1:AN = ~(8'b00000001);  //Display first segment          
           4'h2: begin
               AN = ~(8'b00000000);
               CA = Cath [1];
           end
           4'h3:AN = ~(8'b00000010);
           4'h4: begin
               AN = ~(8'b00000000);
               CA = Cath [2];
           end
           4'h5:AN = ~(8'b00000100);
           4'h6: begin
               AN = ~(8'b00000000);
               CA = Cath [3];
           end
           4'h7:AN = ~(8'b00001000);
           4'h8: begin
               AN = ~(8'b00000000);
               CA = Cath [4];
           end
           4'h9:AN = ~(8'b00010000);
           4'hA: begin
               AN = ~(8'b00000000);
               CA = Cath [5];
           end
           4'hB:AN = ~(8'b00100000);
           4'hC: begin
               AN = ~(8'b00000000);
               CA = Cath [6];
           end
           4'hD: AN = ~(8'b01000000);
           4'hE: begin
               AN = ~(8'b00000000);
               CA = Cath [7];
           end
           4'hF: AN = ~(8'b10000000);
           default:AN = ~(8'b00000000);
       endcase 
       i = i + 4'b0001;
   end
endmodule

module ALU(
    input [15:0] A, B,
    input [2:0] alu_s,
    output reg [15:0] C);
    
    always@(*) begin
        case(alu_s)
            3'b000: C = A + B;   //ADD
            3'b001: C = A - B;   //SUB
            3'b010: C = A & B;   //AND
            3'b011: C = A | B;   //OR
            3'b100: C = A ^ B;   //XOR
            3'b101: C = ~A;      //NOT
            3'b110: C = A <<< 1; //SLA
            3'b111: C = A >>> 1; //SRA
        endcase
    end
endmodule

module memory(
    input clk,
    input rd, wr,
    input [7:0] addr,
    input [15:0] W_data,
    output reg [15:0] R_data);
    
    integer i;
    reg [15:0] ram [0:255];
    
    initial begin
        for(i=0; i<256; i=i+1) begin //initialize all values to 0
            ram[i] = 16'h0000;
        end
        ram[201] = 16'h95C9;
        ram[202] = 16'h96CA;
    end
    
    always@(posedge clk) begin
        if(wr)
            ram[addr] <= W_data;
        if(rd)
            R_data <= ram[addr];
    end
endmodule

module RF(
    input clk,
    input W_wr, Rp_rd, Rq_rd,
    input [3:0] W_addr, Rp_addr, Rq_addr,
    input [15:0] W_data,
    output reg [15:0] Rp_data, Rq_data);
    
    integer i;
    reg [15:0] register [0:255];
    
    initial begin
        for(i=0; i<16; i=i+1) begin //initialize all values to 0
            register[i] = 16'h0000;
        end
    end
    
    always@(posedge clk) begin
        if(W_wr)
            register[W_addr] <= W_data;
        if(Rp_rd)
            Rp_data <= register[W_addr];
        if(Rq_rd)
            Rq_data <= register[W_addr];
    end
endmodule

module mux(
    input [bits-1:0] i1, i2, i3, i4,
    input [1:0] sel,
    output reg [bits-1:0] out);
    parameter bits = 8;

    always@(*) begin
        case(sel)
            2'b00: out = i1;
            2'b01: out = i2;
            2'b10: out = i3;
            2'b11: out = i4;
        endcase
    end
endmodule

module controller(
    input clk, zero_flag,
    input [15:0] IR_d,
    output [7:0] D_addr, RF_W_data,
    output [3:0] W_addr, Rp_addr, Rq_addr,
    output reg [2:0] ALU_sel,
    output [1:0] RF_sel,
    output D_rd, D_wr, W_wr, Rp_rd, Rq_rd, IR_ld, D_addr_sel, PC_inc, PC_clr, PC_ld);
    
    always@(posedge clk) begin
        case(IR_d[15:12])
            4'b1000: ;//LI
            4'b1001: ;//LW
            4'b1010: ;//SW
            4'b1011: ;//BIZ
            4'b1100: ;//BNZ
            4'b1101: ;//JAL
            4'b1110: ;//JMP
            4'b1111: ;//JR
            default: ALU_sel = IR_d[14:12];
        endcase
    end
endmodule

module Instruction_Register(
    input clk, ld, 
    input [15:0] R_data,
    output reg [15:0] out);
    
    always @(posedge clk)
        if(ld)
            out <= R_data;
endmodule

module Program_Counter(
    input clk, PC_inc, PC_clr, PC_ld,
    input [7:0] data_in,
    output reg [7:0] count);
    
    always @(posedge clk)
        if(PC_clr)
            count <= 0;
        else if(PC_ld)
            count <= data_in;
        else if(PC_inc)
            count <= count + 1;
endmodule