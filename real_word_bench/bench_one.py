#!/usr/bin/env python3

import subprocess
import time
import os
import sys
import tempfile
import psutil

def run_command(cmd, cwd=None, monitor_memory=False):
    """Run a command and return the execution time in seconds and peak memory usage in bytes."""
    start_time = time.time()
    max_memory = 0
    try:
        process = subprocess.Popen(cmd, cwd=cwd, stdout=subprocess.PIPE, stderr=subprocess.PIPE, text=True)
        if monitor_memory:
            p = psutil.Process(process.pid)
            while process.poll() is None:
                try:
                    memory = p.memory_info().rss
                    max_memory = max(max_memory, memory)
                    time.sleep(0.1)
                except (psutil.NoSuchProcess, psutil.AccessDenied):
                    break
        process.wait()
        if process.returncode != 0:
            print(f"Error running command: {cmd}")
            print(f"Error output: {process.stderr.read()}")
            sys.exit(1)
    except subprocess.CalledProcessError as e:
        print(f"Error running command: {cmd}")
        print(f"Error output: {e.stderr}")
        sys.exit(1)
    end_time = time.time()
    return end_time - start_time, max_memory

def main():
    if len(sys.argv) != 2:
        print("Usage: python bench_one.py <pltl_formula>")
        sys.exit(1)

    pltl_formula = sys.argv[1]
    
    # Create a temporary directory
    with tempfile.TemporaryDirectory() as temp_dir:
        # Run pltl2dra with fixed output directory
        print(f"Running pltl2dra on formula: {pltl_formula}")
        # Create output directory
        os.makedirs(os.path.join(temp_dir, "output"), exist_ok=True)
        pltl2dra_time, peak_memory = run_command(["/Users/longfangsong/Projects/pltl/target/release/pltl2dra", "-O", os.path.join(temp_dir, "output"), pltl_formula], cwd=temp_dir, monitor_memory=True)
        print(f"pltl2dra execution time: {pltl2dra_time:.2f} seconds")
        print(f"pltl2dra peak memory usage: {peak_memory / 1024 / 1024:.2f} MB")

        # Use the fixed output directory
        generated_dir = os.path.join(temp_dir, "output")
        if not os.path.exists(generated_dir):
            print("Error: Output directory 'output' was not created by pltl2dra")
            sys.exit(1)
        
        # Run make in the output directory
        print("Running make in the output directory")
        make_time, _ = run_command(["make", "-j12"], cwd=generated_dir)
        print(f"make execution time: {make_time:.2f} seconds")

        # Print total time
        total_time = pltl2dra_time + make_time
        print(f"Total execution time: {total_time:.2f} seconds")

        

if __name__ == "__main__":
    main()
