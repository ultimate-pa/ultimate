#include <stdio.h>
#include <assert.h>
#include <math.h>
#include <stdlib.h>
#include <time.h>

///////////////////////////////////////////////////////////////////////////////
// Define input sequences
#define INPUT_MIN 1
#define INPUT_MAX 10
#define INPUT_COUNT (INPUT_MAX - INPUT_MIN + 1)
#define INPUT_SEQ_LENGTH 150

#define ERR_INVALID_INPUT 999
// Flag that contains the number of the label reached, or negative if none
int ERR;

// Array of inputs
int INPUT_SEQ[INPUT_SEQ_LENGTH];

int SHORTEST_SEQ_TO_ERR[100];

void __VERIFIER_error(int i) {
	if (ERR >= 0) {
		fprintf(stderr, "Error not reset. Overwriting error code %d.\n", ERR);
	}
	ERR = i;
}

// Reinitialize automaton, see implementation below
void reset_eca();

// Reset flag
void reset_error() {
	ERR = -1;
}

void calculate_output(int);

// Print INPUT_SEQ before the given position
void print_input(int inputPos) {
	for (int i = 0; i < inputPos; ++i) {
		printf(" %d", INPUT_SEQ[i]);
	}
	printf("\n");
}

// Change the program state to the state after entering the first n values from INPUTS[]
void reset_to_state_at_input(int inputPos) {
	reset_error();
	reset_eca();
	for (int i = 0; i <= inputPos; ++i) {
		calculate_output(INPUT_SEQ[i]);
	}
}


// Fills a given array with "shuffle {INPUT_MIN..INPUT_MAX}"
void fill_input(int* inputLayer) {
	for (int i = 0; i < INPUT_COUNT; ++i) {
		inputLayer[i] = INPUT_MIN + i;
	}
	for (int i = 0; i < INPUT_COUNT - 1; ++i) {
		int j = i + rand() % (INPUT_COUNT - i);
		int swap = inputLayer[j];
		inputLayer[j] = inputLayer[i];
		inputLayer[i] = swap;
	}
}

// Depth-first search possible inputs (branches with errors and invalid inputs are pruned)
void dfs(int depth) {
	if (ERR >= 0) {
		if (ERR != ERR_INVALID_INPUT && depth < SHORTEST_SEQ_TO_ERR[ERR]) {
			SHORTEST_SEQ_TO_ERR[ERR] = depth;
			printf("error_%d -> %d:", ERR, depth);
			print_input(depth);
		}
		return;
	} else if (depth >= INPUT_SEQ_LENGTH) {
		return;
	}
	int inputLayer[INPUT_COUNT];
	fill_input(inputLayer);
	for (int i = 0; i < INPUT_COUNT; ++i) {
		int nextInput = inputLayer[i];
		INPUT_SEQ[depth] = nextInput;
		calculate_output(nextInput);
		dfs(depth + 1);
		reset_to_state_at_input(depth - 1);
	}
}

int main(int argc, char *argv[]) {
	srand(time(NULL));
	for (int i = 0; i < 100; ++i) {
		SHORTEST_SEQ_TO_ERR[i] = INPUT_SEQ_LENGTH + 1;
	}

	reset_eca();
	reset_error();
	dfs(0);
}

/////////////////////////////////////////////////////////////////////////////

// inputs
