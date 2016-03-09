package de.uni_freiburg.informatik.ultimatetest;

public class DirectoryFileEndingsPair {
	private final String mDirectory;
	private final String[] mFileEndings;
	private final int mLimit;

	public DirectoryFileEndingsPair(String directory, String[] fileEndings) {
		super();
		mDirectory = directory;
		mFileEndings = fileEndings;
		mLimit = Integer.MAX_VALUE;
	}

	public DirectoryFileEndingsPair(String directory, String[] fileEndings, int limit) {
		super();
		mDirectory = directory;
		mFileEndings = fileEndings;
		mLimit = limit;
	}

	public String getDirectory() {
		return mDirectory;
	}

	public String[] getFileEndings() {
		return mFileEndings;
	}

	public int getLimit() {
		return mLimit;
	}
	
	@Override
	public String toString() {
		return mDirectory+" "+mFileEndings+" "+mLimit;
	}
}