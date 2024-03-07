BOUND_N=5;
BOUND_M=10;
REPEATS=1;
METHODS="integral linear";
EQUS="direct recursive";
PARALLEL=1;

tsp -S $PARALLEL;

for n in $(seq 2 1 $BOUND_N)
do
    for m in $(seq 2 1 $BOUND_M)
    do
        for r in $(seq 1 1 $REPEATS)
        do
            for method in $METHODS
            do
                for equ in $EQUS
                do
                    echo "sage almost_commuting.sage -run $n $m $equ $method"
                    sage almost_commuting.sage -run $n $m $equ $method 
                done
            done
        done
    done
done
