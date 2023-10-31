BOUND_N=5;
BOUND_M=5;
REPEATS=1;
METHODS="linear diff";
EQUS="direct recursive";
PARALLEL=1;

tsp -S $PARALLEL;

for l in $(seq 3 1 $(($BOUND_N+$BOUND_M)))
do
    for m in $(seq $(( $l-$BOUND_N > 1 ? $l-$BOUND_N : 1 )) 1 $(( $BOUND_M < $l-2 ? $BOUND_M : $l-2 )))
    do
        for r in $(seq 1 1 $REPEATS)
        do
            for method in $METHODS
            do
                for equ in $EQUS
                do
                    tsp sage quasi_commuting.sage $n $m $method $equ
                done
            done
        done
    done
done
