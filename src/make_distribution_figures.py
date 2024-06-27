import os
import z3
import matplotlib.pyplot as plt
import pickle
import random
from collections import defaultdict
from tqdm import tqdm
from concurrent.futures import ProcessPoolExecutor, as_completed

from samplers import VariabilityModel
from samplers.diversity_promotion import DiversityPromotionSampler
from samplers.distance_based import DistanceBasedSampler

fm_path = '../dimacs/small/final'
ground_truth_path = '../out/final'
# ground_truth_path = '../out/testing_dimacs'

# this is where the saved dicts go
out_path = '../out/distribution_figures'

num_times = 400  # sample 100 times TODO: this needs to be larger
# num_times = 1000  # sample 100 times TODO: this needs to be larger


def sample_ground_truth(ground_truth: set, n: int) -> set:
    # ohne zurücklegen ziehen
    return set(random.sample(ground_truth, n))


def serialize_model(model: z3.ModelRef) -> frozenset:
    serialized = set()
    for d in model.decls():
        value = model[d]
        serialized.add((str(d), bool(value)))
    return frozenset(serialized)


def perform_sampling(fm_path, base_name, gt, n_samples):
    vm_dp = VariabilityModel(f'{fm_path}/{base_name}')
    vm_db = VariabilityModel(f'{fm_path}/{base_name}')
    dps = DiversityPromotionSampler(vm_dp)
    dbs = DistanceBasedSampler(vm_db)

    s_dp = dps.sample(n_samples)
    s_db = dbs.sample(n_samples)

    # serialize the models becuase python cant save ModelRefs (ctype pointers) to disk
    ss_dp = {serialize_model(c) for c in s_dp}
    ss_db = {serialize_model(c) for c in s_db}
    s_gt = sample_ground_truth(gt, n_samples)

    return ss_dp, ss_db, s_gt


if __name__ == '__main__':
    # print the directory
    print(os.listdir(ground_truth_path))
    for ground_truth in tqdm(os.listdir(ground_truth_path), desc="Files"):
        print(f'Processing {ground_truth}')
        if ground_truth == 'berkeleydb.dimacs.pickle' or ground_truth == 'blasted_case21.cnf.pickle':
            # skip
            print(f'skipping {ground_truth}')
            continue
            
        with open(f'{ground_truth_path}/{ground_truth}', 'rb') as f:
            gt = pickle.load(f)
        # remove the .pickle extension
        base_name = ground_truth.replace('.pickle', '')

        n_samples = len(gt) // 100  # sample 1% of the ground truth
        # n_samples = 4  # sample 1% of the ground truth
        print(f'Sampling {n_samples} samples {num_times} times')
        d = {'DP': defaultdict(int), 'DB': defaultdict(int), 'GT': defaultdict(int)}

        with ProcessPoolExecutor() as executor:
            futures = [executor.submit(perform_sampling, fm_path, base_name, gt, n_samples) for _ in range(num_times)]

            for future in tqdm(as_completed(futures), desc="Iterations", total=num_times, leave=False):
                s_dp, s_db, s_gt = future.result()

                # Update counts for DP samples
                for sample in s_dp:
                    d['DP'][sample] += 1

                # Update counts for DB samples
                for sample in s_db:
                    d['DB'][sample] += 1

                # Update counts for GT samples
                for sample in s_gt:
                    d['GT'][sample] += 1


        # Prepare data for plotting
        max_count = 0
        multiplicities = {'DP': defaultdict(int), 'DB': defaultdict(int), 'GT': defaultdict(int)}

        # save multiplicities
        with open(f'{out_path}/{base_name}_{num_times}_{n_samples}.pickle', 'wb') as f:
            pickle.dump(d, f)

        for method, counts in d.items():
            for sample, count in counts.items():
                multiplicities[method][count] += 1
                max_count = max(max_count, count)

        # Plotting
        x = range(1, max_count + 1)

        plt.figure(figsize=(10, 6))
        for method, mults in multiplicities.items():
            y = [mults.get(i, 0) for i in x]
            plt.plot(x, y, label=method)

        plt.xlabel('Count (Number of Times a Configuration Appears)')
        plt.ylabel('Number of Samples')
        plt.title(f'Dist for {base_name}')
        plt.legend()
        plt.show()
        # plt.savefig(f'{out_path}/{base_name}_{num_times}_{n_samples}.png')
