package de.uni_freiburg.informatik.ultimate.witnessparser.yaml;

public class Location {

	private final String mFileName;
	private final String mFileHash;
	private final int mLine;
	private final int mColumn;
	private final String mFunction;

	public Location(final String fileName, final String fileHash, final int line, final int column,
			final String function) {
		mFileName = fileName;
		mFileHash = fileHash;
		mLine = line;
		mColumn = column;
		mFunction = function;
	}

	public String getFileName() {
		return mFileName;
	}

	public String getFileHash() {
		return mFileHash;
	}

	public int getLine() {
		return mLine;
	}

	public int getColumn() {
		return mColumn;
	}

	public String getFunction() {
		return mFunction;
	}

	@Override
	public String toString() {
		return "(" + mLine + ", " + mColumn + ")";
	}
}
