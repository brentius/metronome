"""The v2 RTL source list (info.yaml order) and simulator settings shared by the v2 cocotb benches."""
import os
from pathlib import Path

ROOT = Path(__file__).resolve().parents[3]
SRC = Path(os.environ.get("RTL_V2_SRC", ROOT / "src"))   # override: mutation checks on a copy
SOURCES = ["project.v", "md2_host.v", "md2_cfg_bank.v", "cells_behav.v", "md2_line.v", "md2_thread.v", "md2_core.v",
           "md2_acc.v", "md2_shifter.v", "md2_counter.v", "md2_lfsr.v", "md2_mem.v", "md2_stream.v", "md2_pmem.v",
           "md2_dmem.v", "md2_sram_bb.v"]
SRAM_MODEL = [ROOT / "test/sram_model" / f for f in ("RM_IHPSG13_1P_256x64_c2_bm_bist.v",
                                                     "RM_IHPSG13_1P_512x32_c2_bm_bist.v",
                                                     "RM_IHPSG13_1P_core_behavioral_bm_bist.v")]


def rtl_files(ihp_sram=True):
    """(sources, defines): the IHP SRAM behavioural models (as test/Makefile) or md2_pmem/md2_dmem's own arrays."""
    files = [SRC / f for f in SOURCES]
    defines = {"SIM": 1, "COCOTB_SIM": 1}   # COCOTB_SIM: the latch bank's write-spacing check
    if ihp_sram:
        files = SRAM_MODEL + files
        defines.update({"FUNCTIONAL": 1, "USE_IHP_SRAM": 1})
    return files, defines
