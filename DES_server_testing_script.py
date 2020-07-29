import csv
import math
import multiprocessing
import os
import random
import time
import warnings

import DESops as d


def my_fn(args):
    start_time = time.process_time()
    fn_results = d.my_fn(args)
    duration = time.process_time() - start_time

    results = []
    results.append(fn_results)
    results.append(duration)
    queue.put(results)


def write_toprows(DATA_FNAME, SUCCESS_RATE_FNAME):
    if os.path.isfile(DATA_FNAME):
        warnings.warn("{} file exists already, appending data".format(DATA_FNAME))

    else:
        # Headers for excel
        toprow = ["V", "E", "Euc", "Euo", "output", "time (s)"]
        with open(DATA_FNAME, "a") as file:
            writer = csv.writer(file)
            writer.writerow(toprow)

    if os.path.isfile(SUCCESS_RATE_FNAME):
        warnings.warn(
            "{} file exists already, appending data".format(SUCCESS_RATE_FNAME)
        )

    else:
        with open(SUCCESS_RATE_FNAME, "a") as file:
            writer = csv.writer(file)
            writer.writerow(
                ["V", "E", "Euc", "Euo", "total", "my_fn finish", "timeout (s)"]
            )


if __name__ == "__main__":
    # csv for individual tests; written every inner loop
    DATA_FNAME = "mtest1.csv"
    # csv for success rates (did it finish before the timeout)

    SUCCESS_RATE_FNAME = "mtest1_rates.csv"
    write_toprows(DATA_FNAME, SUCCESS_RATE_FNAME)

    TIMEOUT = 30  # seconds - 0 if no timeout - 300 = 5 minutes

    E = 12
    ITER = 20
    Euc = 5
    Euo = 5
    rdeg = 5
    warnings.filterwarnings("ignore")

    for V in range(50, 2000, 50):
        print("Vertices: {}".format(V))
        total = 0
        success = 0
        for i in range(ITER):
            # Generate random DFA (using whichever method)
            g = d.random_DFA.generate(
                V, E, Euc, Euo, timeout=60, max_out_degree=rdeg, max_parallel_edges=2
            )

            num_crit = 1
            X_crit = set()
            X_crit.update(str(s) for s in random.sample(range(V - 1), k=num_crit))

            results = None

            # Use queue to get outputs
            q = multiprocessing.Queue()
            # multiprocessing Process object: target is the function handle, defined above
            #   args can be a tuple, and can use named-arguments
            pc = multiprocessing.Process(target=my_fn, args=(args))
            pc.start()

            # Starts the timout
            pc.join(TIMEOUT)

            # Executes after TIMEOUT seconds:
            if pc.is_alive():
                # End the task
                pc.terminate()
                # Failed to complete in time
                print("my_fn Failed")

            else:
                # If the process isn't alive after timeout, that means it finished
                # This executes when process ends (might be before TIMEOUT)
                success += 1
                results = q.get()

            total += 1

            data_row = [V, E, Euc, Euo, *results]

            with open(DATA_FNAME, "a") as file:
                writer = csv.writer(file)
                writer.writerow(data_row)

        rate_row = [V, E, Euc, Euo, total, success, TIMEOUT]

        with open(SUCCESS_RATE_FNAME, "a") as file:
            writer = csv.writer(file)
            writer.writerow(rate_row)
