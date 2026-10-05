seed = 21101
seqfile = matched-synthetic.txt
Imapfile = matched-synthetic.Imap.txt
jobname = result
speciesdelimitation = 0
speciestree = 0
speciesmodelprior = 1
species&tree = 4 K C L H
  9 7 14 2
  (((H,L),C),K);
phase = 1 1 1 1
usedata = 1
nloci = 5
cleandata = 0
thetaprior = gamma 2 2000
tauprior = gamma 2 1000
finetune = 1
print = 1 0 0 1
burnin = 20000
sampfreq = 20
nsample = 5000
threads = 1
