import os
import matplotlib.pyplot as plt
import pickle
import random
from collections import defaultdict
from tqdm import tqdm
from concurrent.futures import ThreadPoolExecutor, as_completed

from samplers import VariabilityModel
from samplers.diversity_promotion import DiversityPromotionSampler
from samplers.distance_based import DistanceBasedSampler


fm_path = '../dimacs/small/final'
ground_truth_path = '../out/final'

num_times = 100  # sample 100 times
# num_times = 3  # sample 100 times


def sample_ground_truth(ground_truth: set, n: int) -> set:
    # ohne zurücklegen ziehen
    return set(random.sample(ground_truth, n))

if __name__ == '__main__':
    for ground_truth in os.listdir(ground_truth_path):
        with open(f'{ground_truth_path}/{ground_truth}', 'rb') as f:
            gt = pickle.load(f)
        # remove the .pickle extension
        base_name = ground_truth.replace('.pickle', '')

        # n_samples = len(gt) // 10  # sample 10% of the ground truth
        n_samples = 50 # sample 10% of the ground truth
        print(f'Sampling {n_samples} samples {num_times} times')
        d = {'DP': defaultdict(int), 'DB': defaultdict(int), 'GT': defaultdict(int)}
        for iteration in tqdm(range(num_times), desc="Iterations", leave=False):
            # reinit every time since the VM keeps track of which samples have already been drawn
            vm_dp = VariabilityModel(f'{fm_path}/{base_name}')
            vm_db = VariabilityModel(f'{fm_path}/{base_name}')
            dps = DiversityPromotionSampler(vm_dp)
            dbs = DistanceBasedSampler(vm_db)

            s_dp = dps.sample(n_samples)
            s_db = dbs.sample(n_samples)
            # convert Model Refs to strings
            s_dp = {str(c) for c in s_dp}
            s_db = {str(c) for c in s_db}

            s_gt = sample_ground_truth(gt, n_samples)

            # Update counts for DP samples
            for sample in s_dp:
                d['DP'][sample] += 1

            # Update counts for DB samples
            for sample in s_db:
                d['DB'][sample] += 1

            # Update counts for GT samples
            for sample in s_gt:
                d['GT'][sample] += 1

        # Print the counts
        # for method, counts in d.items():
        #     print(f'Counts for {method}:')
        #     for sample, count in counts.items():
        #         if count > 1:
        #             print(f'{method} -> {count}
        # Prepare data for plotting
        max_count = 0
        multiplicities = {'DP': defaultdict(int), 'DB': defaultdict(int), 'GT': defaultdict(int)}

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
        plt.title('Frequency Distribution of Samples')
        plt.legend()
        plt.show()

