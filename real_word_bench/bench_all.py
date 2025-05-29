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
    def read_file_lines(filename):
        with open(filename, 'r') as f:
            return [line.strip() for line in f.readlines()]

    try:
        code_this = read_file_lines('real_word_bench/code_this.txt')
        code_goal = read_file_lines('real_word_bench/code_goal.txt')
        code_ud = read_file_lines('real_word_bench/code_ud.txt')
    except FileNotFoundError as e:
        print(f"Cannot find file - {e.filename}")
        sys.exit(1)

    # formulas = zip(code_goal, code_this, code_ud)
    # for i, (goal, this, ud) in enumerate(formulas):
    for i, this in enumerate(code_this):
        print(f"mkdir /tmp/output{i}")
        print(f"time /Users/longfangsong/Projects/pltl/target/release/pltl2dra -O /tmp/output{i} \"{this}\"")
    for i, _ in enumerate(code_this):
        print(f"cd /tmp/output{i} && time make -j12 > /dev/null")
    for i, ud in enumerate(code_ud):
        print(f"time /Users/longfangsong/Projects/pLTL2TNGBA/pLTL2TNGBA \"{ud}\" > /tmp/temp{i}.hoa")
    for i, ud in enumerate(code_ud):
        print(f"time autfilt --gra --generic --complete -D -S -o /tmp/temp{i}.hoa /tmp/temp{i}.hoa")
    for i, goal in enumerate(code_goal):
        print(f"time /Applications/GOAL.app/Contents/Resources/Java/gc translate \"{goal}\" > /tmp/temp{i}.xml")
    for i, _ in enumerate(code_this):
        print(f"time /Applications/GOAL.app/Contents/Resources/Java/gc determinization -m modifiedsafra -o /tmp/temp{i}-d.hoa /tmp/temp{i}.xml")
    
    for i, this in enumerate(code_this):
        print(f"mkdir /tmp/output{i}")
        print(f"gtime -f \"%M\" /Users/longfangsong/Projects/pltl/target/release/pltl2dra -O /tmp/output{i} \"{this}\"")
    for i, _ in enumerate(code_this):
        print(f"cd /tmp/output{i} && gtime -f \"%M\" make -j12 > /dev/null")
    
    # for i, ud in enumerate(code_ud):
    #     print(f"gtime -f \"%M\" /Users/longfangsong/Projects/pLTL2TNGBA/pLTL2TNGBA \"{ud}\" > /tmp/temp{i}.hoa")
    for i, _ in enumerate(code_ud):
        print(f"gtime -f \"%M\" autfilt --gra --generic --complete -D -S -o /tmp/temp{i}.hoa /tmp/temp{i}.hoa")
    
    # for i, goal in enumerate(code_goal):
    #     print(f"gtime -f \"%M\" /Applications/GOAL.app/Contents/Resources/Java/gc translate \"{goal}\" > /tmp/temp{i}.xml")
    for i, _ in enumerate(code_this):
        print(f"gtime -f \"%M\" /Applications/GOAL.app/Contents/Resources/Java/gc determinization -m modifiedsafra -o /tmp/temp{i}-d.hoa /tmp/temp{i}.xml")
    
    
        # print("cd ./output")
        # print("time make -j12")
        # print("cd ..")
        # print("time /Users/longfangsong/Projects/pLTL2TNGBA/pLTL2TNGBA {ud}")
        # print("time /Applications/GOAL.app/Contents/Resources/Java/gc {goal}")
    # 创建临时目录
    # with tempfile.TemporaryDirectory() as temp_dir:
        # for i, (goal, this, ud) in enumerate(formulas):
            # os.makedirs(os.path.join(temp_dir, "output"), exist_ok=True)
            
            # pltl2dra_time, pltl2dra_mem = run_command(
            #     ["/Users/longfangsong/Projects/pltl/target/release/pltl2dra", 
            #      "-O", os.path.join(temp_dir, "output"), 
            #      this],
            #     cwd=temp_dir,
            #     monitor_memory=True
            # )
            
            # make_time, _ = run_command(["make"], cwd=os.path.join(temp_dir, "output"))
            
            # pltl2tngba_time, pltl2tngba_mem = run_command(
            #     ["/Users/longfangsong/Projects/pLTL2TNGBA/pLTL2TNGBA", ud],
            #     monitor_memory=True
            # )
            
            # gc_time, gc_mem = run_command(
            #     ["/Applications/GOAL.app/Contents/Resources/Java/gc", goal],
            #     monitor_memory=True
            # )
            
            # print(f"case {i}: " +
            #       f"pltl2dra+make(cpu={pltl2dra_time+make_time:.2f}s,mem={pltl2dra_mem/1024:.2f}KB), " +
            #       f"pLTL2TNGBA(cpu={pltl2tngba_time:.2f}s,mem={pltl2tngba_mem/1024:.2f}KB), " +
            #       f"gc(cpu={gc_time:.2f}s,mem={gc_mem/1024:.2f}KB)")

        

if __name__ == "__main__":
    main()
