package de.uni_freiburg.informatik.ultimate.plugins.analysis.abstractinterpretationMk2;

import java.util.List;

/**
 * For keeping track whether sequential compositions are in parallel or not and
 * if so of the merged states so far.
 * 
 * @author GROSS-JAN
 *
 */
class AIVisitorStackElement {
	private List<StackState> mCurrentRootStates;
	private List<StackState> mResultingStates;
	private boolean mProcessInParallel;

	/**
	 * An element representing either parallel or sequential execution of code
	 * blocks
	 * 
	 * @param processInParallel
	 *            if true the code blocks are each processed with rootStates as
	 *            starting states
	 * @param rootStates
	 *            each code block will be processes using this
	 */
	public AIVisitorStackElement(boolean processInParallel,
			List<StackState> rootStates) {
		mProcessInParallel = processInParallel;
		mResultingStates = null;
		mCurrentRootStates = rootStates;
	}

	/**
	 * The state from which upon each parallel sequence does stuff
	 * 
	 * @return
	 */
	public List<StackState> getRootStates() {
		return mCurrentRootStates;
	}

	public List<StackState> getResultingStates() {
		return mResultingStates;
	}

	public void setResultingStates(List<StackState> states) {
		mResultingStates = states;
	}

	public boolean getProcessInParalell() {
		return mProcessInParallel;
	}
}