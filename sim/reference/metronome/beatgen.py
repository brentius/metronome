"""Beat generator (SPEC 3)."""


class BeatGen:
    def __init__(self, g):
        self.g = g
        self.reset()

    def reset(self):
        self.INC = self.MOD = self.T0 = self.T1 = self.T2 = self.PRE = self.WLO = self.WHI = 0
        self.WEN = 0
        self.EDGE_PIN = 0
        self.EDGE_POL = 0
        self.PH = 0
        self.RUN = self.ARM = self.REN = self.SC = self.SP = 0
        self.beat = 0
        self.taps = (0, 0, 0)
        self.seg = 0
        self._nx = None

    def comb(self, rs, fl):
        """Evaluate cycle-t combinational values and the default next state (no commit)."""
        PH, MOD = self.PH, self.MOD
        pin, pol = self.EDGE_PIN, self.EDGE_POL
        edge = 0
        if pin < 13 and pol:
            edge = int(bool((pol & 1) and (rs >> pin) & 1) or bool((pol & 2) and (fl >> pin) & 1))
        if self.WLO <= self.WHI:
            inwin = self.WLO <= PH <= self.WHI
        else:
            inwin = PH >= self.WLO or PH <= self.WHI
        start = edge and self.ARM and not self.RUN
        accept = edge and self.RUN and self.REN and (not self.WEN or inwin)
        beat = 0
        taps = [0, 0, 0]
        nx = PH
        if self.RUN and not accept:
            n = PH + self.INC                      # 17-bit
            wrap = n >= MOD
            nx = n - MOD if wrap else n
            beat = int(wrap)
            for k, tk in enumerate((self.T0, self.T1, self.T2)):
                if tk < MOD:
                    hit = (tk > PH or tk <= nx) if wrap else (PH < tk <= nx)
                    taps[k] = int(hit)
        if start or accept:
            ph_n = self.PRE
        elif self.RUN:
            ph_n = nx & 0xFFFF       # SPEC-AMBIGUITY: nx may be 17-bit when INC >= 2*MOD; compared untruncated, stored truncated
        else:
            ph_n = PH
        self.beat = beat
        self.taps = tuple(taps)
        self.seg = (PH >= self.T0 and self.T0 < MOD) + (PH >= self.T1 and self.T1 < MOD) + (PH >= self.T2 and self.T2 < MOD)
        self._nx = dict(
            PH=ph_n,
            RUN=int(bool(self.RUN or start)),
            ARM=int(bool(self.ARM and not start)),
            SC=1 if accept else (0 if beat else self.SC),
            SP=self.SC if beat else self.SP,
        )

    def commit(self, ctl_move=None):
        n = self._nx
        if ctl_move is not None:           # move to BGg.CTL overrides RUN', ARM', REN'
            n["RUN"], n["ARM"], self.REN = ctl_move & 1, (ctl_move >> 1) & 1, (ctl_move >> 2) & 1
        self.PH, self.RUN, self.ARM, self.SC, self.SP = n["PH"], n["RUN"], n["ARM"], n["SC"], n["SP"]
