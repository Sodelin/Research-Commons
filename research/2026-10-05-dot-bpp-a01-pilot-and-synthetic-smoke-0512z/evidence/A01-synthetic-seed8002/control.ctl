seed = 8002
seqfile = synthetic.txt
Imapfile = synthetic.Imap.txt
jobname = result
speciesdelimitation = 0
speciestree = 1 0.4 0.2 0.1
speciesmodelprior = 1
species&tree = 4 K C L H
  2 2 2 2
  (((K,H),L),C);
phase = 1 1 1 1
usedata = 1
nloci = 5
cleandata = 0
model = JC69
clock = 1
thetaprior = gamma 2 2000
tauprior = gamma 2 1000
finetune = 1
print = 1 0 0 0
burnin = 8000
sampfreq = 2
nsample = 20000
threads = 1
