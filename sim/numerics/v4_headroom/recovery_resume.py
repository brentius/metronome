import os,signal
for pid in (20848,22739):
 os.kill(pid,signal.SIGCONT)
 print('SIGCONT',pid)
