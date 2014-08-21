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
import org.xml.sax.SAXException;
import de.uni_freiburg.informatik.ultimate.core.controllers.ExternalUltimateCore;
import de.uni_freiburg.informatik.ultimate.core.coreplugin.toolchain.ToolchainData;
import de.uni_freiburg.informatik.ultimate.core.preferences.UltimatePreferenceInitializer;
import de.uni_freiburg.informatik.ultimate.core.services.ILoggingService;
import de.uni_freiburg.informatik.ultimate.core.services.IUltimateServiceProvider;
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

	private final UltimateRunDefinition m_UltimateRunDefinition;
	private long mDeadline;

	private String mLogPattern;
	private File mLogFile;
	private IUltimateServiceProvider mCurrentSerivces;
	private final ExternalUltimateCore mExternalUltimateCore;



	public UltimateStarter(UltimateRunDefinition ultimateRunDefinition, long deadline) {
		this(ultimateRunDefinition, deadline, null, null);
	}

	public UltimateStarter(UltimateRunDefinition ultimateRunDefintion, long deadline, File logFile,
			String logPattern) {
		m_UltimateRunDefinition = ultimateRunDefintion;
		mLogger = Logger.getLogger(UltimateStarter.class);
		mExternalUltimateCore = new ExternalUltimateCoreTest(this);
		mDeadline = deadline;
		mLogFile = logFile;
		mLogPattern = logPattern;
		detachLogger();
	}

	public void runUltimate() throws Throwable {
		mExternalUltimateCore.runUltimate();
	}

	@Override
	public int init(ICore core, ILoggingService loggingService) {
		return mExternalUltimateCore.init(core, loggingService, 
				m_UltimateRunDefinition.getSettings(), mDeadline, 
				m_UltimateRunDefinition.getInput(), null);
	}
	
	public void complete() {
		mExternalUltimateCore.complete();
	}

	private void attachLogger() {
		if (mLogFile == null) {
			return;
		}

		detachLogger();
		try {
			mAppender = new FileAppender(new PatternLayout(mLogPattern), mLogFile.getAbsolutePath());
			mLogger.addAppender(mAppender);
		} catch (IOException e1) {
			detachLogger();
			mLogger.fatal("Failed to create logfile " + mLogFile + ". Reason: " + e1);
		}
	}

	private void detachLogger() {
		if (mAppender == null) {
			return;
		}
		mLogger.removeAppender(mAppender);
	}

	@Override
	public String getPluginName() {
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
	public ToolchainData selectTools(List<ITool> tools) {
		try {
			ToolchainData tc = new ToolchainData(m_UltimateRunDefinition.getToolchain().getAbsolutePath());
			mCurrentSerivces = tc.getServices();
			mLogger.info("Loaded toolchain from " + m_UltimateRunDefinition.getToolchain().getAbsolutePath());
			return tc;
		} catch (FileNotFoundException | JAXBException | SAXException e) {
			mLogger.fatal("Toolchain could not be created from file " + m_UltimateRunDefinition.getToolchain() + ": " + e);
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

	public IUltimateServiceProvider getServices() {
		return mCurrentSerivces;
	}
	
	private class ExternalUltimateCoreTest extends ExternalUltimateCore{

		public ExternalUltimateCoreTest(IController controller) {
			super(controller);
		}
		
		@Override
		protected Logger getLogger(ILoggingService loggingService) {
			mLogger = super.getLogger(loggingService);
			attachLogger();
			return mLogger;
		}
		
		@Override
		public void complete() {
			detachLogger();
			super.complete();
		}
		
	}
}
