package de.uni_freiburg.informatik.ultimate.plugins.analysis.abstractinterpretationMk2;

/**
 * For keeping track whether sequential
 * compositions are in parallel or not
 * and if so of the merged states so far.
 * 
 * @author GROSS-JAN
 *
 */
class AIVisitorStackElement
{
	private StackState mState;
	private boolean mProcessInParallel;
	
	public AIVisitorStackElement(boolean processInParallel)
	{
		mProcessInParallel = processInParallel;
		mState = null;
	}
	
	public StackState getState()
	{
		return mState;
	}
	
	public void setState(StackState state)
	{
		mState = state;
	}
	
	public boolean getProcessInParalell()
	{
		return mProcessInParallel;
	}
}