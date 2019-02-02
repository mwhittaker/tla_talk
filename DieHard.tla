-------------------------------- MODULE DieHard --------------------------------

\* https://youtu.be/6cAbgAaEOVE

EXTENDS Integers

VARIABLE small, big

Init ==
  /\ small = 0
  /\ big = 0

FillSmall ==
  /\ small' = 3
  /\ big' = big

FillBig ==
  /\ big' = 5
  /\ small' = small

EmptySmall ==
  /\ small' = 0
  /\ big' = big

EmptyBig ==
  /\ big' = 0
  /\ small' = small

BigToSmall ==
  IF big + small <= 3 THEN
    /\ small' = small + big
    /\ big' = 0
  ELSE
    /\ small' = 3
    /\ big' = big - (3 - small)

SmallToBig ==
  IF big + small <= 5 THEN
    /\ big' = small + big
    /\ small' = 0
  ELSE
    /\ big' = 5
    /\ small' = small - (5 - big)

Next ==
  \/ FillSmall
  \/ FillBig
  \/ EmptySmall
  \/ EmptyBig
  \/ BigToSmall
  \/ SmallToBig

TypeOk ==
  /\ small \in 0..3
  /\ big \in 0..5

FourGallons ==
  \/ small = 4
  \/ big = 4

NotFourGallons == ~FourGallons

================================================================================
