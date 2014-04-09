package de.uni_freiburg.informatik.ultimatetest;

import java.io.File;
import java.io.FileNotFoundException;
import java.io.IOException;
import java.util.Collection;
import java.util.List;

import javax.xml.bind.JAXBException;

import org.apache.log4j.FileAppender;
import org.apache.log4j.Logger;
import org.apache.log4j.PatternLayout;
import org.eclipse.equinox.app.IApplication;
import org.xml.sax.SAXException;

import de.uni_freiburg.informatik.ultimate.core.coreplugin.UltimateCore;
import de.uni_freiburg.informatik.ultimate.core.coreplugin.toolchain.BasicToolchainJob;
import de.uni_freiburg.informatik.ultimate.core.coreplugin.toolchain.DefaultToolchainJob;
import de.uni_freiburg.informatik.ultimate.core.coreplugin.toolchain.Toolchain;
import de.uni_freiburg.informatik.ultimate.core.preferences.UltimatePreferenceInitializer;
import de.uni_freiburg.informatik.ultimate.ep.interfaces.IController;
import de.uni_freiburg.informatik.ultimate.ep.interfaces.ICore;
import de.uni_freiburg.informatik.ultimate.ep.interfaces.ISource;
import de.uni_freiburg.informatik.ultimate.ep.interfaces.ITool;

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
public class UltimateStarter implements IController {

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

	public UltimateStarter(File inputFile, File settingsFile, File toolchainFile, long deadline) {
		this(inputFile, settingsFile, toolchainFile, deadline, null, null);
	}

	public UltimateStarter(File inputFile, File settingsFile, File toolchainFile, long deadline, File logFile,
			String logPattern) {
		mLogger = Logger.getLogger(UltimateStarter.class);
		mInputFile = inputFile;
		mToolchainFile = toolchainFile;
		if (mInputFile == null || mToolchainFile == null) {
			throw new IllegalArgumentException("Toolchain and Input may not be null");
		}
		mSettingsFile = settingsFile;
		mDeadline = deadline;
		mLogFile = logFile;
		mLogPattern = logPattern;
		detachLogger();
	}

	public void runUltimate() throws Exception {
		if (mCurrentUltimateInstance != null) {
			throw new Exception("You must call complete() before re-using this instance ");
		}
		mCurrentUltimateInstance = new UltimateCore();
		mCurrentUltimateInstance.start(this, false);
	}

	@Override
	public int init(ICore core) {
		if (core == null) {
			return -1;
		}

		if (mSettingsFile != null) {
			core.loadPreferences(mSettingsFile.getAbsolutePath());
		}
		attachLogger();

		core.setDeadline(System.currentTimeMillis() + mDeadline);

		try {
			BasicToolchainJob tcj = new DefaultToolchainJob("Processing Toolchain", core, this,
					BasicToolchainJob.ChainMode.RUN_TOOLCHAIN, mInputFile, null);
			tcj.schedule();
			// in non-GUI mode, we must wait until job has finished!
			tcj.join();

		} catch (InterruptedException e) {
			mLogger.error("Exception in Toolchain", e);
			return -1;
		}

		return IApplication.EXIT_OK;
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
			mAppender = new FileAppender(new PatternLayout(mLogPattern), mLogFile.getAbsolutePath());
			Logger.getRootLogger().addAppender(mAppender);
		} catch (IOException e1) {
			detachLogger();
			mLogger.fatal("Failed to create logfile " + mLogFile + ". Reason: " + e1);
		}
	}

	private void detachLogger() {
		if (mAppender == null) {
			return;
		}
		Logger.getRootLogger().removeAppender(mAppender);
	}

	@Override
	public String getName() {
		return "UltimateStarter";
	}

	@Override
	public String getPluginID() {
		return "UltimateStarter";
	}

	@Override
	public UltimatePreferenceInitializer getPreferences() {
		return null;
	}

	@Override
	public ISource selectParser(Collection<ISource> parser) {
		mLogger.fatal("UltimateStarter does not support the selection of parsers by the user!");
		return null;
	}

	@Override
	public Toolchain selectTools(List<ITool> tools) {
		try {
			return new Toolchain(mToolchainFile.getAbsolutePath());
		} catch (FileNotFoundException | JAXBException | SAXException e) {
			mLogger.fatal("Toolchain could not be created from file " + mToolchainFile + ": " + e);
			return null;
		}
	}

	@Override
	public List<String> selectModel(List<String> modelNames) {
		mLogger.fatal("UltimateStarter does not support the selection of models by the user!");
		return null;
	}

	@Override
	public void displayToolchainResultProgramIncorrect() {

	}

	@Override
	public void displayToolchainResultProgramCorrect() {

	}

	@Override
	public void displayToolchainResultProgramUnknown(String description) {

	}

	@Override
	public void displayException(String description, Throwable ex) {

	}

}
