BOUND_N="2 3 5 7";
BOUND_M=15;
REPEATS=10;
METHODS="integral linear";
EQUS="direct recursive";

for m in $(seq 2 1 $BOUND_M)
do
    for n in $BOUND_N
    do
        for r in $(seq 1 1 $REPEATS)
        do
            sage almost_commuting.sage -run $n $m direct integral 
            sleep 15
        done
    done
done
