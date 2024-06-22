#!/usr/bin/env python

# Read from a JSONL file specified on the command line
# and read out the "task_id", "prompt", "entry_point", "canonical_solution", 
# and "test" fields into a Task object.

import json
import argparse
import re
import os

class Task:
    def __init__(self, task_id, prompt, entry_point, canonical_solution, test):
        self.task_id = task_id
        # Parse task number from task_id written as "HumanEval/task_num"
        self.task_num = int(re.search(r'\d+', task_id).group())
        self.prompt = prompt
        self.entry_point = entry_point
        self.canonical_solution = canonical_solution
        self.test = test

    def __str__(self):
        return f"Task {self.task_id}: {self.prompt}\nEntry point: {self.entry_point}\nCanonical solution: {self.canonical_solution}\nTest: {self.test}"
        #return f"Task num {self.task_num}"
    
    def __repr__(self):
        return self.__str__()

    def to_verus_task(self):
        verus_str = f"""
/*
### ID
{self.task_id}
*/

/*
### VERUS BEGIN
*/
use vstd::prelude::*;

verus! {{

 

}} // verus!

fn main() {{}}

/*
### VERUS END
*/

/*
### PROMPT
{self.prompt}
*/

/*
### ENTRY POINT
{self.entry_point}
*/

/*
### CANONICAL SOLUTION
{self.canonical_solution}
*/

/*
### TEST
{self.test}
*/

"""
        return verus_str

def read_tasks_from_jsonl(file):
    tasks = []
    with open(file, 'r') as f:
        for line in f:
            task = json.loads(line)
            tasks.append(Task(task['task_id'], task['prompt'], task['entry_point'], task['canonical_solution'], task['test']))
    return tasks

def print_tasks(tasks, out_dir):
    if not os.path.exists(out_dir):
        os.makedirs(out_dir)

    for task in tasks:
        file_path = os.path.join(out_dir, f"human_eval_{str(task.task_num).zfill(3)}.rs")
        with open(file_path, 'w') as f:
            f.write(task.to_verus_task())

def main():
    parser = argparse.ArgumentParser(description='Convert JSONL file of HumanEval tasks to Verus tasks')
    parser.add_argument('-j', '--jsonl', type=str, help='JSONL file to read from', required=True)
    parser.add_argument('--out', type=str, help='Directory to write Verus tasks', required=True)
    args = parser.parse_args()

    tasks = read_tasks_from_jsonl(args.jsonl)
    print(tasks[0].to_verus_task())
    print_tasks(tasks, args.out)

if __name__ == '__main__':
    main()