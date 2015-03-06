package de.uni_freiburg.informatik.ultimate.witnessparser.graph;

import de.uni_freiburg.informatik.ultimate.model.location.ILocation;
import de.uni_freiburg.informatik.ultimate.result.Check;

public class WitnessLocation implements ILocation{

	private final String mFilename;
	private int mStartLine;
	private int mEndLine;
	private int mStartColumn;
	private int mEndColumn;

	public WitnessLocation(String filename, int line){
		mFilename = filename;
		mStartLine = line;
		mEndLine = line;
		mStartColumn = 0;
		mEndColumn = 0;
	}
	
	@Override
	public String getFileName() {
		return mFilename;
	}

	@Override
	public int getStartLine() {
		return mStartLine;
	}

	@Override
	public int getEndLine() {
		return mEndLine;
	}

	@Override
	public int getStartColumn() {
		return mStartColumn;
	}

	@Override
	public int getEndColumn() {
		return mEndColumn;
	}

	@Override
	public ILocation getOrigin() {
		throw new UnsupportedOperationException();
	}

	@Override
	public Check getCheck() {
		throw new UnsupportedOperationException();
	}

	@Override
	public boolean isLoop() {
		throw new UnsupportedOperationException();
	}

}
