#include "simif_emul.h"
#include <cassert>
#include <cmath>
#include <memory>
#include <verilated.h>
#if VM_TRACE
#include <verilated_vcd_c.h>
#endif // VM_TRACE

extern uint64_t main_time;
extern Vverilator_top *top;
#if VM_TRACE
extern VerilatedVcdC *tfp;
#endif // VM_TRACE

void tick() {
  assert(simif_emul_t::cpu_managed_axi4 != nullptr);
  assert(simif_emul_t::master != nullptr);

  // ASSUMPTION: All models have *no* combinational paths through I/O
  // Step 1: Clock lo -> propagate signals between DUT and software models
  top->ctrl_aw_valid = simif_emul_t::master->aw_valid();
  top->ctrl_aw_bits_id = simif_emul_t::master->aw_id();
  top->ctrl_aw_bits_addr = simif_emul_t::master->aw_addr();
  top->ctrl_aw_bits_size = simif_emul_t::master->aw_size();
  top->ctrl_aw_bits_len = simif_emul_t::master->aw_len();

  top->ctrl_ar_valid = simif_emul_t::master->ar_valid();
  top->ctrl_ar_bits_id = simif_emul_t::master->ar_id();
  top->ctrl_ar_bits_addr = simif_emul_t::master->ar_addr();
  top->ctrl_ar_bits_size = simif_emul_t::master->ar_size();
  top->ctrl_ar_bits_len = simif_emul_t::master->ar_len();

  top->ctrl_w_valid = simif_emul_t::master->w_valid();
  top->ctrl_w_bits_strb = simif_emul_t::master->w_strb();
  top->ctrl_w_bits_last = simif_emul_t::master->w_last();

  top->ctrl_r_ready = simif_emul_t::master->r_ready();
  top->ctrl_b_ready = simif_emul_t::master->b_ready();
  memcpy(
      &top->ctrl_w_bits_data, simif_emul_t::master->w_data(), CTRL_BEAT_BYTES);

#ifdef CPU_MANAGED_AXI4_PRESENT
  top->cpu_managed_axi4_aw_valid = simif_emul_t::cpu_managed_axi4->aw_valid();
  top->cpu_managed_axi4_aw_bits_id = simif_emul_t::cpu_managed_axi4->aw_id();
  top->cpu_managed_axi4_aw_bits_addr =
      simif_emul_t::cpu_managed_axi4->aw_addr();
  top->cpu_managed_axi4_aw_bits_size =
      simif_emul_t::cpu_managed_axi4->aw_size();
  top->cpu_managed_axi4_aw_bits_len = simif_emul_t::cpu_managed_axi4->aw_len();

  top->cpu_managed_axi4_ar_valid = simif_emul_t::cpu_managed_axi4->ar_valid();
  top->cpu_managed_axi4_ar_bits_id = simif_emul_t::cpu_managed_axi4->ar_id();
  top->cpu_managed_axi4_ar_bits_addr =
      simif_emul_t::cpu_managed_axi4->ar_addr();
  top->cpu_managed_axi4_ar_bits_size =
      simif_emul_t::cpu_managed_axi4->ar_size();
  top->cpu_managed_axi4_ar_bits_len = simif_emul_t::cpu_managed_axi4->ar_len();

  top->cpu_managed_axi4_w_valid = simif_emul_t::cpu_managed_axi4->w_valid();
  top->cpu_managed_axi4_w_bits_strb = simif_emul_t::cpu_managed_axi4->w_strb();
  top->cpu_managed_axi4_w_bits_last = simif_emul_t::cpu_managed_axi4->w_last();

  top->cpu_managed_axi4_r_ready = simif_emul_t::cpu_managed_axi4->r_ready();
  top->cpu_managed_axi4_b_ready = simif_emul_t::cpu_managed_axi4->b_ready();
#if CPU_MANAGED_AXI4_DATA_BITS > 64
  memcpy(top->cpu_managed_axi4_w_bits_data,
         simif_emul_t::cpu_managed_axi4->w_data(),
         CPU_MANAGED_AXI4_BEAT_BYTES);
#else
  memcpy(&top->cpu_managed_axi4_w_bits_data,
         simif_emul_t::cpu_managed_axi4->w_data(),
         CPU_MANAGED_AXI4_BEAT_BYTES);
#endif
#endif // CPU_MANAGED_AXI4_PRESENT

#ifdef FPGA_MANAGED_AXI4_PRESENT
  top->fpga_managed_axi4_aw_ready = simif_emul_t::cpu_mem->aw_ready();
  top->fpga_managed_axi4_ar_ready = simif_emul_t::cpu_mem->ar_ready();
  top->fpga_managed_axi4_w_ready = simif_emul_t::cpu_mem->w_ready();
  top->fpga_managed_axi4_b_valid = simif_emul_t::cpu_mem->b_valid();
  top->fpga_managed_axi4_b_bits_id = simif_emul_t::cpu_mem->b_id();
  top->fpga_managed_axi4_b_bits_resp = simif_emul_t::cpu_mem->b_resp();
  top->fpga_managed_axi4_r_valid = simif_emul_t::cpu_mem->r_valid();
  top->fpga_managed_axi4_r_bits_id = simif_emul_t::cpu_mem->r_id();
  top->fpga_managed_axi4_r_bits_resp = simif_emul_t::cpu_mem->r_resp();
  top->fpga_managed_axi4_r_bits_last = simif_emul_t::cpu_mem->r_last();
#if MEM_DATA_BITS > 64
  memcpy(top->fpga_managed_axi4_r_bits_data,
         simif_emul_t::cpu_mem->r_data(),
         FPGA_MANAGED_AXI4_DATA_BITS / 8);
#else
  memcpy(&top->fpga_managed_axi4_r_bits_data,
         simif_emul_t::cpu_mem->r_data(),
         FPGA_MANAGED_AXI4_DATA_BITS / 8);
#endif
#endif // FPGA_MANAGED_AXI4_PRESENT

  top->mem_0_aw_ready = simif_emul_t::slave[0]->aw_ready();
  top->mem_0_ar_ready = simif_emul_t::slave[0]->ar_ready();
  top->mem_0_w_ready = simif_emul_t::slave[0]->w_ready();
  top->mem_0_b_valid = simif_emul_t::slave[0]->b_valid();
  top->mem_0_b_bits_id = simif_emul_t::slave[0]->b_id();
  top->mem_0_b_bits_resp = simif_emul_t::slave[0]->b_resp();
  top->mem_0_r_valid = simif_emul_t::slave[0]->r_valid();
  top->mem_0_r_bits_id = simif_emul_t::slave[0]->r_id();
  top->mem_0_r_bits_resp = simif_emul_t::slave[0]->r_resp();
  top->mem_0_r_bits_last = simif_emul_t::slave[0]->r_last();
#if MEM_DATA_BITS > 64
  memcpy(
      top->mem_0_r_bits_data, simif_emul_t::slave[0]->r_data(), MEM_BEAT_BYTES);
#else
  memcpy(&top->mem_0_r_bits_data,
         simif_emul_t::slave[0]->r_data(),
         MEM_BEAT_BYTES);
#endif
#ifdef MEM_HAS_CHANNEL1
  top->mem_1_aw_ready = simif_emul_t::slave[1]->aw_ready();
  top->mem_1_ar_ready = simif_emul_t::slave[1]->ar_ready();
  top->mem_1_w_ready = simif_emul_t::slave[1]->w_ready();
  top->mem_1_b_valid = simif_emul_t::slave[1]->b_valid();
  top->mem_1_b_bits_id = simif_emul_t::slave[1]->b_id();
  top->mem_1_b_bits_resp = simif_emul_t::slave[1]->b_resp();
  top->mem_1_r_valid = simif_emul_t::slave[1]->r_valid();
  top->mem_1_r_bits_id = simif_emul_t::slave[1]->r_id();
  top->mem_1_r_bits_resp = simif_emul_t::slave[1]->r_resp();
  top->mem_1_r_bits_last = simif_emul_t::slave[1]->r_last();
#if MEM_DATA_BITS > 64
  memcpy(
      top->mem_1_r_bits_data, simif_emul_t::slave[1]->r_data(), MEM_BEAT_BYTES);
#else
  memcpy(&top->mem_1_r_bits_data,
         simif_emul_t::slave[1]->r_data(),
         MEM_BEAT_BYTES);
#endif
#endif // MEM_HAS_CHANNEL1

#ifdef MEM_HAS_CHANNEL2
  top->mem_2_aw_ready = simif_emul_t::slave[2]->aw_ready();
  top->mem_2_ar_ready = simif_emul_t::slave[2]->ar_ready();
  top->mem_2_w_ready = simif_emul_t::slave[2]->w_ready();
  top->mem_2_b_valid = simif_emul_t::slave[2]->b_valid();
  top->mem_2_b_bits_id = simif_emul_t::slave[2]->b_id();
  top->mem_2_b_bits_resp = simif_emul_t::slave[2]->b_resp();
  top->mem_2_r_valid = simif_emul_t::slave[2]->r_valid();
  top->mem_2_r_bits_id = simif_emul_t::slave[2]->r_id();
  top->mem_2_r_bits_resp = simif_emul_t::slave[2]->r_resp();
  top->mem_2_r_bits_last = simif_emul_t::slave[2]->r_last();
#if MEM_DATA_BITS > 64
  memcpy(
      top->mem_2_r_bits_data, simif_emul_t::slave[2]->r_data(), MEM_BEAT_BYTES);
#else
  memcpy(&top->mem_2_r_bits_data,
         simif_emul_t::slave[2]->r_data(),
         MEM_BEAT_BYTES);
#endif
#endif // MEM_HAS_CHANNEL2

#ifdef MEM_HAS_CHANNEL3
  top->mem_3_aw_ready = simif_emul_t::slave[3]->aw_ready();
  top->mem_3_ar_ready = simif_emul_t::slave[3]->ar_ready();
  top->mem_3_w_ready = simif_emul_t::slave[3]->w_ready();
  top->mem_3_b_valid = simif_emul_t::slave[3]->b_valid();
  top->mem_3_b_bits_id = simif_emul_t::slave[3]->b_id();
  top->mem_3_b_bits_resp = simif_emul_t::slave[3]->b_resp();
  top->mem_3_r_valid = simif_emul_t::slave[3]->r_valid();
  top->mem_3_r_bits_id = simif_emul_t::slave[3]->r_id();
  top->mem_3_r_bits_resp = simif_emul_t::slave[3]->r_resp();
  top->mem_3_r_bits_last = simif_emul_t::slave[3]->r_last();
#if MEM_DATA_BITS > 64
  memcpy(
      top->mem_3_r_bits_data, simif_emul_t::slave[3]->r_data(), MEM_BEAT_BYTES);
#else
  memcpy(&top->mem_3_r_bits_data,
         simif_emul_t::slave[3]->r_data(),
         MEM_BEAT_BYTES);
#endif
#endif // MEM_HAS_CHANNEL3

  top->eval();
#if VM_TRACE
  if (tfp)
    tfp->dump((double)main_time);
#endif // VM_TRACE
  main_time++;

  top->clock = 0;
  top->eval(); // This shouldn't do much
#if VM_TRACE
  if (tfp)
    tfp->dump((double)main_time);
#endif // VM_TRACE
  main_time++;

  // Step 2: Clock high, tick all software models and evaluate DUT with posedge
  simif_emul_t::master->tick(top->reset,
                             top->ctrl_ar_ready,
                             top->ctrl_aw_ready,
                             top->ctrl_w_ready,
                             top->ctrl_r_bits_id,
                             &top->ctrl_r_bits_data,
                             top->ctrl_r_bits_last,
                             top->ctrl_r_valid,
                             top->ctrl_b_bits_id,
                             top->ctrl_b_valid);

#ifdef CPU_MANAGED_AXI4_PRESENT
  simif_emul_t::cpu_managed_axi4->tick(top->reset,
                                       top->cpu_managed_axi4_ar_ready,
                                       top->cpu_managed_axi4_aw_ready,
                                       top->cpu_managed_axi4_w_ready,
                                       top->cpu_managed_axi4_r_bits_id,
                                       &top->cpu_managed_axi4_r_bits_data,
                                       top->cpu_managed_axi4_r_bits_last,
                                       top->cpu_managed_axi4_r_valid,
                                       top->cpu_managed_axi4_b_bits_id,
                                       top->cpu_managed_axi4_b_valid);
#endif // CPU_MANAGED_AXI4_PRESENT

#ifdef FPGA_MANAGED_AXI4_PRESENT
  simif_emul_t::cpu_mem->tick(top->reset,
                              top->fpga_managed_axi4_ar_valid,
                              top->fpga_managed_axi4_ar_bits_addr,
                              top->fpga_managed_axi4_ar_bits_id,
                              top->fpga_managed_axi4_ar_bits_size,
                              top->fpga_managed_axi4_ar_bits_len,

                              top->fpga_managed_axi4_aw_valid,
                              top->fpga_managed_axi4_aw_bits_addr,
                              top->fpga_managed_axi4_aw_bits_id,
                              top->fpga_managed_axi4_aw_bits_size,
                              top->fpga_managed_axi4_aw_bits_len,

                              top->fpga_managed_axi4_w_valid,
#if FPGA_MANAGED_AXI4_STRB_BITS > 64
                              &top->fpga_managed_axi4_w_bits_strb,
#else
                              top->fpga_managed_axi4_w_bits_strb,
#endif
#if FPGA_MANAGED_AXI4_DATA_BITS > 64
                              &top->fpga_managed_axi4_w_bits_data,
#else
                              top->fpga_managed_axi4_w_bits_data,
#endif
                              top->fpga_managed_axi4_w_bits_last,

                              top->fpga_managed_axi4_r_ready,
                              top->fpga_managed_axi4_b_ready);
#endif // FPGA_MANAGED_AXI4_PRESENT

  simif_emul_t::slave[0]->tick(top->reset,
                               top->mem_0_ar_valid,
                               top->mem_0_ar_bits_addr,
                               top->mem_0_ar_bits_id,
                               top->mem_0_ar_bits_size,
                               top->mem_0_ar_bits_len,

                               top->mem_0_aw_valid,
                               top->mem_0_aw_bits_addr,
                               top->mem_0_aw_bits_id,
                               top->mem_0_aw_bits_size,
                               top->mem_0_aw_bits_len,

                               top->mem_0_w_valid,
                               top->mem_0_w_bits_strb,
#if MEM_DATA_BITS > 64
                               top->mem_0_w_bits_data,
#else
                               &top->mem_0_w_bits_data,
#endif
                               top->mem_0_w_bits_last,

                               top->mem_0_r_ready,
                               top->mem_0_b_ready);

#ifdef MEM_HAS_CHANNEL1
  simif_emul_t::slave[1]->tick(top->reset,
                               top->mem_1_ar_valid,
                               top->mem_1_ar_bits_addr,
                               top->mem_1_ar_bits_id,
                               top->mem_1_ar_bits_size,
                               top->mem_1_ar_bits_len,

                               top->mem_1_aw_valid,
                               top->mem_1_aw_bits_addr,
                               top->mem_1_aw_bits_id,
                               top->mem_1_aw_bits_size,
                               top->mem_1_aw_bits_len,

                               top->mem_1_w_valid,
                               top->mem_1_w_bits_strb,
#if MEM_DATA_BITS > 64
                               top->mem_1_w_bits_data,
#else
                               &top->mem_1_w_bits_data,
#endif
                               top->mem_1_w_bits_last,

                               top->mem_1_r_ready,
                               top->mem_1_b_ready);
#endif // MEM_HAS_CHANNEL1
#ifdef MEM_HAS_CHANNEL2
  simif_emul_t::slave[2]->tick(top->reset,
                               top->mem_2_ar_valid,
                               top->mem_2_ar_bits_addr,
                               top->mem_2_ar_bits_id,
                               top->mem_2_ar_bits_size,
                               top->mem_2_ar_bits_len,

                               top->mem_2_aw_valid,
                               top->mem_2_aw_bits_addr,
                               top->mem_2_aw_bits_id,
                               top->mem_2_aw_bits_size,
                               top->mem_2_aw_bits_len,

                               top->mem_2_w_valid,
                               top->mem_2_w_bits_strb,
#if MEM_DATA_BITS > 64
                               top->mem_2_w_bits_data,
#else
                               &top->mem_2_w_bits_data,
#endif
                               top->mem_2_w_bits_last,

                               top->mem_2_r_ready,
                               top->mem_2_b_ready);
#endif // MEM_HAS_CHANNEL2
#ifdef MEM_HAS_CHANNEL3
  simif_emul_t::slave[3]->tick(top->reset,
                               top->mem_3_ar_valid,
                               top->mem_3_ar_bits_addr,
                               top->mem_3_ar_bits_id,
                               top->mem_3_ar_bits_size,
                               top->mem_3_ar_bits_len,

                               top->mem_3_aw_valid,
                               top->mem_3_aw_bits_addr,
                               top->mem_3_aw_bits_id,
                               top->mem_3_aw_bits_size,
                               top->mem_3_aw_bits_len,

                               top->mem_3_w_valid,
                               top->mem_3_w_bits_strb,
#if MEM_DATA_BITS > 64
                               top->mem_3_w_bits_data,
#else
                               &top->mem_3_w_bits_data,
#endif
                               top->mem_3_w_bits_last,

                               top->mem_3_r_ready,
                               top->mem_3_b_ready);
#endif // MEM_HAS_CHANNEL3

  top->clock = 1;
  top->eval();
}
