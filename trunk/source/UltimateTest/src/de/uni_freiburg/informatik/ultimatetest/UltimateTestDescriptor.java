package de.uni_freiburg.informatik.ultimatetest;

import java.io.File;

public class UltimateTestDescriptor {
	public File getPathSettings() {
		return mPathSettings;
	}

	public void setPathSettings(String pathSettings) {
		this.mPathSettings = new File(pathSettings);
	}

	public File getPathToolchain() {
		return mPathToolchain;
	}

	public void setPathToolchain(String pathToolchain) {
		this.mPathToolchain = new File(pathToolchain);
	}

	public File getPathInputFile() {
		return mPathInputFileDirectory;
	}

	public void setPathInputFile(String pathInputFileDirectory) {
		this.mPathInputFileDirectory = new File(pathInputFileDirectory);
	}

	public String getFileEnding() {
		return mFileEnding;
	}

	public void setFileEnding(String fileEndings) {
		this.mFileEnding = fileEndings;
	}

	public int getDeadline() {
		return mDeadline;
	}

	public void setDeadline(int deadline) {
		this.mDeadline = deadline;
	}

	public UltimateTestDescriptor copy() {
		return new UltimateTestDescriptor(mPathSettings, mPathToolchain,
				mPathInputFileDirectory, mFileEnding, mDeadline);
	}

	public UltimateTestDescriptor copy(String pathToFile) {
		return new UltimateTestDescriptor(mPathSettings, mPathToolchain,
				new File(pathToFile), mFileEnding, mDeadline);
	}

	public UltimateTestDescriptor(String mPathSettings, String mPathToolchain,
			String mPathInputFileDirectory, String mFileEnding,
			 int mDeadline) {
		super();
		this.mPathSettings = new File(mPathSettings);
		this.mPathToolchain = new File(mPathToolchain);
		this.mPathInputFileDirectory = new File(mPathInputFileDirectory);
		this.mFileEnding = mFileEnding;
		this.mDeadline = mDeadline;
	}

	private UltimateTestDescriptor(File mPathSettings, File mPathToolchain,
			File mPathInputFileDirectory, String mFileEnding,
			 int mDeadline) {
		super();
		this.mPathSettings = mPathSettings;
		this.mPathToolchain = mPathToolchain;
		this.mPathInputFileDirectory = mPathInputFileDirectory;
		this.mFileEnding = mFileEnding;
		this.mDeadline = mDeadline;
	}

	private File mPathSettings;
	private File mPathToolchain;
	private File mPathInputFileDirectory;
	private String mFileEnding;
	private int mDeadline;
	
	@Override
	public String toString() {
		return mPathSettings.getName() + " " + mPathToolchain.getName() + " "
				+ mPathInputFileDirectory.getName();
	}

}
