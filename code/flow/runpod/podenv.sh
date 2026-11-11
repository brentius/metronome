# Sourced by the pod scripts. The LibreLane image is Nix-based: pip wheels cannot find shared libraries
# that live in the Nix store, so collect the directories of the ones they need.
_libdirs=""
for _l in libstdc++.so.6 libcairo.so.2 libz.so.1 libffi.so.8; do
  _f=$(ls /nix/store/*/lib/$_l 2>/dev/null | head -1)
  [ -n "$_f" ] && _libdirs="$_libdirs:$(dirname "$_f")"
done
export LD_LIBRARY_PATH="${_libdirs#:}${LD_LIBRARY_PATH:+:$LD_LIBRARY_PATH}"
# tt-support-tools calls `yowasp-yosys`; setup_flow.sh puts a shim in /root/bin that runs the image's native yosys.
export PATH="/root/bin:$PATH"
export PDK_ROOT=${PDK_ROOT:-/root/pdk}
export PDK=${PDK:-ihp-sg13cmos5l}
unset _l _f _libdirs
