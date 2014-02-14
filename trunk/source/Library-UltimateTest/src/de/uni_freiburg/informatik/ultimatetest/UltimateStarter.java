package de.uni_freiburg.informatik.ultimatetest;

import java.io.File;
import java.io.IOException;

import org.apache.log4j.FileAppender;
import org.apache.log4j.Logger;
import org.apache.log4j.PatternLayout;

import de.uni_freiburg.informatik.ultimate.core.coreplugin.UltimateCore;
import de.uni_freiburg.informatik.ultimate.core.coreplugin.UltimateCore.Ultimate_Mode;

/**
 * 
 * This class wraps the Ultimate application and allows to start it without
 * setting an IController object.
 * 
 * Call runUltimate() to execute it and complete after processing the results
 * (to release resources).
 * 
 * @author dietsch
 * 
 */
public class UltimateStarter {

	private Logger mLogger;
	private FileAppender mAppender;

	private File mInputFile;
	private File mSettingsFile;
	private File mToolchainFile;
	private long mDeadline;

	private String mLogPattern;
	private File mLogFile;
	private UltimateCore mCurrentUltimateInstance;

	public UltimateStarter(File inputFile, File toolchainFile, long deadline) {
		this(inputFile, null, toolchainFile, deadline, null, null);
	}

	public UltimateStarter(File inputFile, File settingsFile,
			File toolchainFile, long deadline) {
		this(inputFile, settingsFile, toolchainFile, deadline, null, null);
	}

	public UltimateStarter(File inputFile, File settingsFile,
			File toolchainFile, long deadline, File logFile, String logPattern) {
		mLogger = Logger.getLogger(UltimateStarter.class);
		mInputFile = inputFile;
		mToolchainFile = toolchainFile;
		if (mInputFile == null || mToolchainFile == null) {
			throw new IllegalArgumentException(
					"Toolchain and Input may not be null");
		}
		mSettingsFile = settingsFile;
		mDeadline = deadline;
		mLogFile = logFile;
		mLogPattern = logPattern;
		detachLogger();
	}

	public void runUltimate() throws Exception {
		if (mCurrentUltimateInstance != null) {
			throw new Exception(
					"You must call complete() before re-using this instance ");
		}
		mCurrentUltimateInstance = new UltimateCore(
				Ultimate_Mode.EXTERNAL_EXECUTION);
		mCurrentUltimateInstance.setM_InputFile(mInputFile);
		if (mSettingsFile != null) {
			mCurrentUltimateInstance.setSettingsFile(mSettingsFile);
		}
		mCurrentUltimateInstance.setToolchainXML(mToolchainFile);
		attachLogger();
		mCurrentUltimateInstance.setDeadline(System.currentTimeMillis()
				+ mDeadline);
		mCurrentUltimateInstance.start(null);
	}

	public void complete() {
		detachLogger();
	}
	
	private void attachLogger() {
		if (mLogFile == null) {
			return;
		}

		detachLogger();
		try {
			mAppender = new FileAppender(new PatternLayout(mLogPattern),
					mLogFile.getAbsolutePath());
			Logger.getRootLogger().addAppender(mAppender);
		} catch (IOException e1) {
			detachLogger();
			mLogger.fatal("Failed to create logfile " + mLogFile + ". Reason: "
					+ e1);
		}
	}

	private void detachLogger() {
		if (mAppender == null) {
			return;
		}
		Logger.getRootLogger().removeAppender(mAppender);
	}

}
