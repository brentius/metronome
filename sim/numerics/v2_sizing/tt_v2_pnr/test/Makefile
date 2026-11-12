# Makefile
# See https://docs.cocotb.org/en/stable/quickstart.html for more info

# defaults
SIM ?= icarus
FST ?= -fst # Use more efficient FST format
TOPLEVEL_LANG ?= verilog
SRC_DIR = $(PWD)/../src
# Same order as info.yaml (project.v first: it sets `timescale for the files that have none).
PROJECT_SOURCES = project.v md2_host.v md2_commons_stub.v md2_core.v md2_core_thread.v md2_pmem.v md2_dmem.v \
                  md2_stream.v cfg_latch_bank.v cells_behav.v md2_sram_bb.v

# IHP's behavioural models of the SRAM macros, used in RTL and gate-level simulation (the netlist instantiates the
# macros as cells). FUNCTIONAL selects the models' functional view; SIM empties src/md2_sram_bb.v.
SRAM_MODEL = $(PWD)/sram_model/RM_IHPSG13_1P_256x64_c2_bm_bist.v $(PWD)/sram_model/RM_IHPSG13_1P_512x32_c2_bm_bist.v \
             $(PWD)/sram_model/RM_IHPSG13_1P_core_behavioral_bm_bist.v
VERILOG_SOURCES += $(SRAM_MODEL)
COMPILE_ARGS    += -DFUNCTIONAL -DSIM

ifneq ($(GATES),yes)

# RTL simulation: the IHP SRAM models (USE_IHP_SRAM) and the behavioural latch and clock-gate cells (no USE_IHP_CELLS)
SIM_BUILD				= sim_build/rtl
COMPILE_ARGS    += -DUSE_IHP_SRAM
VERILOG_SOURCES += $(addprefix $(SRC_DIR)/,$(PROJECT_SOURCES))

else

# Gate level simulation:
SIM_BUILD				= sim_build/gl
COMPILE_ARGS    += -DGL_TEST
# Cell models for the PDK in $(PDK) (ihp-sg13cmos5l or ihp-sg13g2), e.g. sg13cmos5l_stdcell.v
PDK ?= ihp-sg13cmos5l
PDK_CELL_PREFIX = $(patsubst ihp-%,%,$(PDK))
PDK_LIBS_REF = $(PDK_ROOT)/$(PDK)/libs.ref
VERILOG_SOURCES += $(PDK_LIBS_REF)/$(PDK_CELL_PREFIX)_io/verilog/$(PDK_CELL_PREFIX)_io.v
# Newer PDK versions ship the UDP (user-defined primitive) models in a separate file
VERILOG_SOURCES += $(wildcard $(PDK_LIBS_REF)/$(PDK_CELL_PREFIX)_stdcell/verilog/$(PDK_CELL_PREFIX)_udp.v)
VERILOG_SOURCES += $(PDK_LIBS_REF)/$(PDK_CELL_PREFIX)_stdcell/verilog/$(PDK_CELL_PREFIX)_stdcell.v

# this gets copied in by the GDS action workflow
VERILOG_SOURCES += $(PWD)/gate_level_netlist.v

endif

# Allow sharing configuration between design and testbench via `include`:
COMPILE_ARGS 		+= -I$(SRC_DIR)

# Include the testbench sources:
VERILOG_SOURCES += $(PWD)/tb.v
TOPLEVEL = tb

# List test modules to run, separated by commas and without the .py suffix:
COCOTB_TEST_MODULES = test

# include cocotb's make rules to take care of the simulator setup
include $(shell cocotb-config --makefiles)/Makefile.sim
