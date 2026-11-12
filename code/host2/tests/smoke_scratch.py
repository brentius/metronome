from common import *
chip = Chip(); p = example("uart_tx"); load(chip, p)
tr = pin_trace(chip, 3, lambda uo,a,b:(uo>>2)&1)
chip.backdoor_write(m.HOST_MAP["CTRL_BASE"]+4, b"\xA5")
tr += pin_trace(chip, 6000, lambda uo,a,b:(uo>>2)&1)
r = runs(tr); print(r[:14])
c=Chip(); load(c,example("eth_tx"))
tr = pin_trace(c, 500, lambda uo,a,b:a&1)
print(runs(tr)[:12], c.threads[0].EN, c.threads[0].LATE, c.lines[0].TAPMISS)
