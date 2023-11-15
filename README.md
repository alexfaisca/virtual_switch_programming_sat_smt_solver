# 1. Brief Description of the Automatic Placement of Rulesets Problem
 
The aim of this project is to find the distribution which minimizes the number of re-circulations in the placement of groups of rules in switches divided into stages. A re-circulation occurs when there is a dependency between two groups of rules (A, B) where B is placed in the same stage in the same switch as A or in a previous stage of the same switch. Each group of rules is placed into only one stage in a switch and the sum of the memory requirements of all the groups placed in a stage do not exceed the memory capacity of that stage (equal for all stages of a switch). It is also not possible given a dependency between two groups of rules (A, B) to place A in a switch succeeding B.


# 2. Running the Code
			
In order to install the necessary dependencies from the main directory run:

### pip3 install -r requirements.md

Following this, to run the project from the main directory simply run the main python file as follows:

## SAT solver:

### python3 project1.py < instance.apr > solution.out

## SMT solver:

### python3 project2.py < instance.apr > solution.out

instance.apr contains the formulation of the problem. 
project1 writes the solution to the standard output, which can, however, be redirected to a certain file (e.g. solution.out).

		



