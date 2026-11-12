Traceback (most recent call last):
  File "/root/work/v2pnr_r1_20261112T0056/./tt/tt_tool.py", line 174, in <module>
    project.summarize(
    ~~~~~~~~~~~~~~~~~^
        print_cell_category=args.print_cell_category,
        ^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^
        print_cell_summary=args.print_cell_summary,
        ^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^
    )
    ^
  File "/root/tt/project.py", line 783, in summarize
    cell_count = self.get_cell_counts_from_gl()
  File "/root/tt/project.py", line 876, in get_cell_counts_from_gl
    with open(self.get_gl_path()) as fh:
              ~~~~~~~~~~~~~~~~^^
  File "/root/tt/project.py", line 352, in get_gl_path
    return glob.glob(
           ~~~~~~~~~~
        os.path.join(self.local_dir, "runs/wokwi/final/nl/*.nl.v")
        ~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~
    )[0]
    ~^^^
IndexError: list index out of range
