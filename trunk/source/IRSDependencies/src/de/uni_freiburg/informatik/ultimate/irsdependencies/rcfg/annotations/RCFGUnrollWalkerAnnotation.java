package de.uni_freiburg.informatik.ultimate.irsdependencies.rcfg.annotations;


import de.uni_freiburg.informatik.ultimate.plugins.generator.rcfgbuilder.cfg.RCFGNode;

public class RCFGUnrollWalkerAnnotation extends IRSDependenciesAnnotation {

	private static final long serialVersionUID = 1L;
	private final String[] mAttribFields = { "IsLoopEntry", "IsLoopExit",
			"Honda", "IsChecked" };
	
	private boolean mIsLoopEntry;
	private boolean mIsLoopExit;
	private RCFGNode mHonda;

	public RCFGUnrollWalkerAnnotation(RCFGNode honda, boolean isEntry,
			boolean isExit) {
		setLoopEntry(isEntry);
		setIsLoopExit(isExit);
		setHonda(honda);
	}
	
	
	@Override
	protected String[] getFieldNames() {
		return mAttribFields;
	}
	
	@Override
	protected Object getFieldValue(String field) {
		switch (field) {
		case "IsLoopEntry":
			return isLoopEntry();
		case "IsLoopExit":
			return isLoopExit();
		case "Honda":
			return getHonda();
		default:
			return null;
		}
	}


	public RCFGNode getHonda() {
		return mHonda;
	}


	public void setHonda(RCFGNode mHonda) {
		this.mHonda = mHonda;
	}


	public boolean isLoopExit() {
		return mIsLoopExit;
	}


	public void setIsLoopExit(boolean mIsLoopExit) {
		this.mIsLoopExit = mIsLoopExit;
	}


	public boolean isLoopEntry() {
		return mIsLoopEntry;
	}


	public void setLoopEntry(boolean mIsLoopEntry) {
		this.mIsLoopEntry = mIsLoopEntry;
	}



}