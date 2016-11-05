"overview-reachability.csv" contains all our results for the reachability problems.

Columns ----------------------------------------
problem number, error number, reachable?, result provider, trace length [, trace...]

Explanation ----------------------------------------
1. problem number
	Number of c-file, for example "10" for "Problem10.c".
2. error number
	Fixed prefix "error_" and number of the error,
	for example "error_0" for "__VERIFIER_error(0)".
3. reachable?
	One of ...
		yes  - error is reachable
		no   - error is not reachable
		unkn - unknown
	"unknown" was abbreviated to prevent accidental selection
	of "unknown" when grep-ing for "no".
4. result provider
	How did we find this result?
	Arbitrary many flags from ...
		b - BFS bruteforcer
		d - DFS bruteforcer
		f - Frama C 
		u - Ultimate
	I only set the flags in the csv when I had the results available.
	Feel free to set additional flags in the csv when you could verify
	the results with another provider (for instance Frama-C).
5. trace length
	Length of the error trace or empty if no error trace is known.
6. trace
	Input sequence leading to the error.
	Each input has its own field in.
	Inputs are entered from left to right. 

RERS Submission ----------------------------------------
We can use the following script to generate our official submission.
	grep -v 'unkn' | cut -d, -f1-3
See also http://rers-challenge.org/2016/index.php?page=submit (scroll down)
