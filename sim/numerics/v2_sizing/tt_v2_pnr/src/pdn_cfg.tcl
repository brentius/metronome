# Metronome v2 PnR sizing: PDN for the Tiny Tapeout IHP SG13CMOS5L tile with SRAM macros.
#
# The commands of LibreLane 3.1.0.dev4's default scripts/openroad/common/pdn_cfg.tcl for the single-layer case that
# Tiny Tapeout uses (FP_PDN_MULTILAYER 0), without the per-macro grid. The tile's PDN is vertical Metal4 stripes,
# the same layer as the SRAM power pins, so a macro grid would have no shapes and pdngen would fail
# (PDN-0232/PDN-0233). The SRAMs are powered by the Project.ExtendPowerStripes step (librelane_plugin_sram_pdn.py),
# which runs right after OpenROAD.GeneratePDN. PDN_MACRO_CONNECTIONS still applies through set_global_connections.

source $::env(SCRIPTS_DIR)/openroad/common/io.tcl
source $::env(SCRIPTS_DIR)/openroad/common/set_global_connections.tcl
set_global_connections

if { $::env(PDN_MULTILAYER) == 1 } {
    throw APPLICATION "src/pdn_cfg.tcl supports only the single-layer Tiny Tapeout PDN (FP_PDN_MULTILAYER 0)."
}

set secondary []
foreach vdd $::env(VDD_NETS) gnd $::env(GND_NETS) {
    if { $vdd != $::env(VDD_NET) } {
        lappend secondary $vdd
        if { [[ord::get_db_block] findNet $vdd] == "NULL" } {
            set net [odb::dbNet_create [ord::get_db_block] $vdd]
            $net setSpecial
            $net setSigType "POWER"
        }
    }
    if { $gnd != $::env(GND_NET) } {
        lappend secondary $gnd
        if { [[ord::get_db_block] findNet $gnd] == "NULL" } {
            set net [odb::dbNet_create [ord::get_db_block] $gnd]
            $net setSpecial
            $net setSigType "GROUND"
        }
    }
}
set_voltage_domain -name CORE -power $::env(VDD_NET) -ground $::env(GND_NET) -secondary_power $secondary

set arg_list [list]
if { $::env(PDN_ENABLE_PINS) } {
    lappend arg_list -pins "$::env(PDN_VERTICAL_LAYER)"
}
define_pdn_grid -name stdcell_grid -starts_with POWER -voltage_domain CORE {*}$arg_list

set arg_list [list]
append_if_equals arg_list PDN_EXTEND_TO "core_ring" -extend_to_core_ring
append_if_equals arg_list PDN_EXTEND_TO "boundary" -extend_to_boundary
add_pdn_stripe \
    -grid stdcell_grid \
    -layer $::env(PDN_VERTICAL_LAYER) \
    -width $::env(PDN_VWIDTH) \
    -pitch $::env(PDN_VPITCH) \
    -offset $::env(PDN_VOFFSET) \
    -spacing $::env(PDN_VSPACING) \
    -starts_with POWER \
    {*}$arg_list

# standard cell rails
if { $::env(PDN_ENABLE_RAILS) == 1 } {
    add_pdn_stripe -grid stdcell_grid -layer $::env(PDN_RAIL_LAYER) -width $::env(PDN_RAIL_WIDTH) -followpins
    add_pdn_connect -grid stdcell_grid -layers "$::env(PDN_RAIL_LAYER) $::env(PDN_VERTICAL_LAYER)"
}

if { $::env(PDN_CORE_RING) == 1 } {
    throw APPLICATION "PDN_CORE_RING needs FP_PDN_MULTILAYER, which this tile does not use."
}
