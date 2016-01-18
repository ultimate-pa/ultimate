/*
 * Copyright (C) 2014-2015 Daniel Dietsch (dietsch@informatik.uni-freiburg.de)
 * Copyright (C) 2015 University of Freiburg
 * 
 * This file is part of the ULTIMATE CDTPlugin plug-in.
 * 
 * The ULTIMATE CDTPlugin plug-in is free software: you can redistribute it and/or modify
 * it under the terms of the GNU Lesser General Public License as published
 * by the Free Software Foundation, either version 3 of the License, or
 * (at your option) any later version.
 * 
 * The ULTIMATE CDTPlugin plug-in is distributed in the hope that it will be useful,
 * but WITHOUT ANY WARRANTY; without even the implied warranty of
 * MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
 * GNU Lesser General Public License for more details.
 * 
 * You should have received a copy of the GNU Lesser General Public License
 * along with the ULTIMATE CDTPlugin plug-in. If not, see <http://www.gnu.org/licenses/>.
 * 
 * Additional permission under GNU GPL version 3 section 7:
 * If you modify the ULTIMATE CDTPlugin plug-in, or any covered work, by linking
 * or combining it with Eclipse RCP (or a modified version of Eclipse RCP), 
 * containing parts covered by the terms of the Eclipse Public License, the 
 * licensors of the ULTIMATE CDTPlugin plug-in grant you additional permission 
 * to convey the resulting work.
 */
package de.uni_freiburg.informatik.ultimate.cdt.codan;

import java.util.ArrayList;
import java.util.Collection;
import java.util.List;
import java.util.concurrent.Semaphore;

import org.apache.log4j.Logger;
import org.eclipse.cdt.core.dom.ast.IASTTranslationUnit;
import org.eclipse.equinox.app.IApplication;

import de.uni_freiburg.informatik.ultimate.cdt.Activator;
import de.uni_freiburg.informatik.ultimate.core.coreplugin.UltimateCore;
import de.uni_freiburg.informatik.ultimate.core.coreplugin.toolchain.ExternalParserToolchainJob;
import de.uni_freiburg.informatik.ultimate.core.coreplugin.toolchain.ToolchainData;
import de.uni_freiburg.informatik.ultimate.core.preferences.UltimatePreferenceInitializer;
import de.uni_freiburg.informatik.ultimate.core.services.model.ILoggingService;
import de.uni_freiburg.informatik.ultimate.ep.interfaces.IController;
import de.uni_freiburg.informatik.ultimate.ep.interfaces.ICore;
import de.uni_freiburg.informatik.ultimate.ep.interfaces.ISource;
import de.uni_freiburg.informatik.ultimate.ep.interfaces.ITool;
import de.uni_freiburg.informatik.ultimate.ep.interfaces.IToolchain;
import de.uni_freiburg.informatik.ultimate.gui.preferencepages.UltimatePreferencePageFactory;
import de.uni_freiburg.informatik.ultimate.model.GraphType;
import de.uni_freiburg.informatik.ultimate.model.GraphType.Type;
import de.uni_freiburg.informatik.ultimate.model.IElement;
import de.uni_freiburg.informatik.ultimate.model.structure.WrapperNode;

/**
 * {@link CDTController} is one of the distinct controllers of Ultimate. It
 * starts the Core from a different host (another RCP instance, namely Eclipse
 * CDT), but uses one {@link ICore} instance for multiple executions of
 * Ultimate.
 * 
 * @author dietsch
 */
public class CDTController implements IController {

	private Logger mLogger;
	private UltimateCChecker mChecker;

	private ICore mUltimate;
	private UltimateThread mUltimateThread;
	private ManualReleaseToolchainJob mCurrentJob;

	private final Semaphore mUltimateExit;
	private final Semaphore mUltimateReady;
	private ToolchainData mToolchainData;

	public CDTController(UltimateCChecker currentChecker) throws Exception {
		mChecker = currentChecker;
		mUltimateExit = new Semaphore(0);
		mUltimateReady = new Semaphore(0);
		initUltimateThread();
	}

	@Override
	public int init(ICore core, ILoggingService loggingService) {
		// we use init() only to create the preference pages and safe a core
		// reference
		mLogger = loggingService.getControllerLogger();
		new UltimatePreferencePageFactory(core).createPreferencePages();
		mUltimate = core;
		// now we wait for the exit command
		mUltimateReady.release();
		mUltimateExit.acquireUninterruptibly();
		return IApplication.EXIT_OK;
	}

	public void runToolchain(String toolchainPath, IASTTranslationUnit ast) throws Exception {
		initUltimateThread();
		mLogger.info("Using toolchain " + toolchainPath);
		mToolchainData = new ToolchainData(toolchainPath);
		mChecker.setServices(mToolchainData.getServices());
		mChecker.setStorage(mToolchainData.getStorage());

		mCurrentJob = new ManualReleaseToolchainJob("Run Ultimate...", mUltimate, this, new WrapperNode(null, ast),
				new GraphType(Activator.PLUGIN_ID, Type.AST, new ArrayList<String>()), mLogger);
		mCurrentJob.setUser(true);
		mCurrentJob.schedule();
		mCurrentJob.join();
	}
	
	private void initUltimateThread() throws Exception {
		if (mUltimateThread == null) {
			mUltimateThread = new UltimateThread(this);
			mUltimateThread.startUltimate();
			mUltimateReady.acquireUninterruptibly();
		} else if (!mUltimateThread.isRunning()) {
			// can only happen if there was an exception
			Exception ex = mUltimateThread.getInnerException();
			complete();
			close();
			throw ex;
		}
	}

	public void close() {
		mUltimateExit.release();
		mUltimateThread = null;
	}

	public void complete() {
		mCurrentJob.releaseLastToolchainManually();
	}

	@Override
	public ToolchainData selectTools(List<ITool> tools) {
		return mToolchainData;
	}

	@Override
	public List<String> selectModel(List<String> modelNames) {
		ArrayList<String> returnList = new ArrayList<String>();
		for (String model : modelNames) {
			if (model
					.contains(de.uni_freiburg.informatik.ultimate.plugins.generator.cacsl2boogietranslator.Activator.PLUGIN_ID)) {
				returnList.add(model);
			}
		}
		if (returnList.isEmpty()) {
			returnList.addAll(modelNames);
		}
		return returnList;
	}

	@Override
	public String getPluginName() {
		return Activator.PLUGIN_ID;
	}

	@Override
	public String getPluginID() {
		return Activator.PLUGIN_ID;
	}

	@Override
	public ISource selectParser(Collection<ISource> parser) {
		throw new UnsupportedOperationException("This method should never be called for this controller!");
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

	@Override
	public UltimatePreferenceInitializer getPreferences() {
		// cdt uses the codan preference handling
		return null;
	}

	private class UltimateThread {

		private final IController mController;
		private Exception mUltimateException;
		private boolean mIsRunning;

		private UltimateThread(IController controller) {
			mController = controller;
		}

		public void startUltimate() {
			Thread t = new Thread(new Runnable() {
				@Override
				public void run() {
					mIsRunning = true;
					// initialize ultimate core in its own thread, which then
					// delegates control to init and should stay there until
					// close() is called
					UltimateCore core = new UltimateCore();
					try {
						core.start(mController, true);
					} catch (Exception e) {
						mUltimateException = e;
					}
					mIsRunning = false;
				}
			},"CDTUltimateThread");
			t.start();
		}

		public boolean isRunning() {
			return mIsRunning;
		}

		public Exception getInnerException() {
			return mUltimateException;
		}
	}

	private class ManualReleaseToolchainJob extends ExternalParserToolchainJob {

		private IToolchain mCurrentChain;

		public ManualReleaseToolchainJob(String name, ICore core, IController controller, IElement ast,
				GraphType outputDefinition, Logger logger) {
			super(name, core, controller, ast, outputDefinition, logger);
		}

		@Override
		protected void releaseToolchain(IToolchain chain) {
			if (mCurrentChain != null && mCurrentChain != chain) {
				// ensure that no chain is unreleased
				super.releaseToolchain(mCurrentChain);
			}
			mCurrentChain = chain;
		}

		protected void releaseLastToolchainManually() {
			if (mCurrentChain != null) {
				super.releaseToolchain(mCurrentChain);
				mCurrentChain = null;
			}
		}

	}
}
