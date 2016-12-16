package de.uni_freiburg.informatik.ultimate.test;

public class DirectoryFileEndingsPair {
	private final String mDirectory;
	private final String[] mFileEndings;
	private final int mOffset;
	private final int mLimit;

	public DirectoryFileEndingsPair(final String file) {
		super();
		mDirectory = file;
		final int index = file.lastIndexOf('.');
		if (index <= 0) {
			throw new IllegalArgumentException(file + " has no valid extension");
		}
		mFileEndings = new String[] { file.substring(index + 1) };
		mOffset = 0;
		mLimit = Integer.MAX_VALUE;
	}

	public DirectoryFileEndingsPair(final String directory, final String[] fileEndings) {
		super();
		mDirectory = directory;
		mFileEndings = fileEndings;
		mOffset = 0;
		mLimit = Integer.MAX_VALUE;
	}

	public DirectoryFileEndingsPair(final String directory, final String[] fileEndings, final int limit) {
		super();
		mDirectory = directory;
		mFileEndings = fileEndings;
		mOffset = 0;
		mLimit = limit;
	}

	public DirectoryFileEndingsPair(final String directory, final String[] fileEndings, final int offset,
			final int limit) {
		super();
		mDirectory = directory;
		mFileEndings = fileEndings;
		mOffset = offset;
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

	public int getOffset() {
		return mOffset;
	}

	@Override
	public String toString() {
		return mDirectory + " " + mFileEndings + " " + mLimit;
	}
}