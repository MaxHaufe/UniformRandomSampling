import os
import pickle
from samplers.naive import NaiveSampler
from samplers import VariabilityModel
from concurrent.futures import ProcessPoolExecutor


def process_file(file, files, output):
    print("Solving: ", file)
    vm1 = VariabilityModel(f'{files}/{file}')
    dps = NaiveSampler(vm1)
    s = dps.sample_all()
    # s = dps.sample(5)
    # convert Model Refs to strings
    s = {str(c) for c in s}
    # save set to disk
    with open(f'{output}/{file}.pickle', 'wb') as f:
        pickle.dump(s, f)


# solve all benchmark problems

files = '../dimacs/small/final'
output = '../out/'


def bench():
    # Collect all files to process
    file_list = os.listdir(files)

    # Create a ProcessPoolExecutor with as many workers as you have CPU cores
    with ProcessPoolExecutor() as executor:
        # Use list comprehension to submit tasks to the executor
        futures = [executor.submit(process_file, file, files, output) for file in file_list]

        # Optionally, you can wait for all futures to complete and handle exceptions
        for future in futures:
            try:
                future.result()  # This will raise an exception if the process failed
            except Exception as e:
                print(f"Exception occurred: {e}")


def print_stats():
    # Collect all files to process
    file_list = os.listdir(output)
    for file in file_list:
        # remove dirs from file list
        if os.path.isdir(f'{output}{file}'):
            continue
        with open(f'{output}{file}', 'rb') as f:
            s = pickle.load(f)

            # if over 2k configs, copy them to out/final
            if len(s) > 2500:
                print(f"{file}: {len(s)}")
                with open(f'{output}final/{file}', 'wb') as f:
                    pickle.dump(s, f)


if __name__ == '__main__':
    # bench()
    print_stats()
