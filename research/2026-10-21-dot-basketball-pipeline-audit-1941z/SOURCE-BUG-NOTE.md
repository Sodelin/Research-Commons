# Why an internally consistent basketball table was quarantined

Author: dot (OpenAI-assisted research), prepared for Nolan. 2026-10-21.

## Verified observations

An institutional 2015–16 derived lineup table contained 1,230 games and 51,054 own-team interval rows. Its intervals passed five-player cardinality, positive-duration, per-quarter duration and complementary home/away net-point checks. These checks were necessary but insufficient.

External checks on two opening-day games found disagreement with final game margins:

- Atlanta–Detroit, 2015-10-27: derived home margin −10; actual 94–106 gives −12. [Official scoreboard](https://www.nba.com/game/0021500001/box-score).
- Chicago–Cleveland, 2015-10-27: derived home margin +4; actual 97–95 gives +2. [Official scoreboard](https://www.nba.com/game/cle-vs-chi-0021500002).

These are two checked examples, not an estimated population error rate. Two further games had nonconsecutive period labels. Chicago–Detroit, 2015-12-18 was a four-overtime game but the source omitted period 6; Washington–Minnesota, 2016-03-25 was a two-overtime game but omitted period 5. [Chicago–Detroit game](https://www.nba.com/game/det-vs-chi-0021500391); [official officiating archive](https://official.nba.com/nba-officiating-last-two-minute-reports-archive/). Therefore merely relabelling the available overtime periods would not reconstruct the missing observations.

## Source-code mechanism and limits

The reviewed author processing routine initializes a quarter's differential from its first recorded post-event differential, rather than necessarily from the preceding quarter's closing score. Telescoping segment changes can therefore omit initial scoring. A separate inner merge uses quarter information assembled from substitution events; a quarter with no recorded substitution can be omitted. These mechanisms are consistent with the observed failures. This is not a proof that every discrepancy in every season has only these causes.

Pinned author code: https://github.com/arnaud-odet/lineup/blob/29f64f982ebeabe68187144ad00aefb1f84fca10/roster_lib/data/season.py . Institutional source: https://doi.org/10.57745/9NVFIQ . No copied upstream raw play-by-play is included here.

## Consequence for our evaluation

A chronological ridge fit completed before the external checks. Its loss improvement described prediction of the source's faulty interval labels, not verified game margins. That interpretation is withdrawn. Player coefficients, comparative losses and resampling summaries from that run are quarantined. No repair was made by distributing scoreboard residuals across intervals, and no missing lineup was invented.

The engineering correction is to require independent target-label validation, in addition to internal conservation. A provenance assertion in software is not itself proof; an audit must establish that the observed labels are correctly reconstructed. Even final-score agreement can conceal cancelling interval errors, so event/interval construction also needs review.

The derived fields do not uniquely specify the omitted scoring increments and missing-period lineups. Proceeding requires a correct permitted source or a verified source reconstruction, not further tuning on these labels. This is a bounded source-quality finding, not a claim that public basketball analytics generally fail or that established metrics are invalid.
