import io

p = 'code/tests/lean/Metronome/ChipCut/Discharge/HostPinWire.lean'
s = io.open(p, encoding='utf-8').read()
start = s.index('/-- `List.any` over a two-element list. -/')
end = s.index('/-- The selected stream at a `Fin` index is the vector entry. -/')
block = s[start:end]
s = s[:start] + s[end:]
anchor = '/-- **`Machine.hostRead` is a `ChipRel` congruence.**'
i = s.index(anchor)
s = s[:i] + block + s[i:]
io.open(p, 'w', encoding='utf-8').write(s)
print('moved', len(block))
