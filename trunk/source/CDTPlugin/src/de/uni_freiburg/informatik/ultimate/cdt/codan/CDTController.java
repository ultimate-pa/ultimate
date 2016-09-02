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
import java.util.Map;
import java.util.concurrent.Semaphore;

import org.eclipse.cdt.core.dom.ast.IASTTranslationUnit;
import org.eclipse.equinox.app.IApplication;

import de.uni_freiburg.informatik.ultimate.cdt.Activator;
import de.uni_freiburg.informatik.ultimate.core.coreplugin.UltimateCore;
import de.uni_freiburg.informatik.ultimate.core.coreplugin.toolchain.ExternalParserToolchainJob;
import de.uni_freiburg.informatik.ultimate.core.lib.models.WrapperNode;
import de.uni_freiburg.informatik.ultimate.core.lib.toolchain.RunDefinition;
import de.uni_freiburg.informatik.ultimate.core.model.IController;
import de.uni_freiburg.informatik.ultimate.core.model.ICore;
import de.uni_freiburg.informatik.ultimate.core.model.ISource;
import de.uni_freiburg.informatik.ultimate.core.model.ITool;
import de.uni_freiburg.informatik.ultimate.core.model.IToolchain;
import de.uni_freiburg.informatik.ultimate.core.model.IToolchainData;
import de.uni_freiburg.informatik.ultimate.core.model.models.IElement;
import de.uni_freiburg.informatik.ultimate.core.model.models.ModelType;
import de.uni_freiburg.informatik.ultimate.core.model.models.ModelType.Type;
import de.uni_freiburg.informatik.ultimate.core.model.preferences.IPreferenceInitializer;
import de.uni_freiburg.informatik.ultimate.core.model.results.IResult;
import de.uni_freiburg.informatik.ultimate.core.model.services.ILogger;
import de.uni_freiburg.informatik.ultimate.gui.preferencepages.UltimatePreferencePageFactory;

/**
 * {@link CDTController} is one of the distinct controllers of Ultimate. It starts the Core from a different host
 * (another RCP instance, namely Eclipse CDT), but uses one {@link ICore<RunDefinition>} instance for multiple
 * executions of Ultimate.
 *
 * @author dietsch
 */
public class CDTController implements IController<RunDefinition> {

	private ILogger mLogger;
	private final UltimateCChecker mChecker;

	private ICore<RunDefinition> mCore;
	private UltimateThread mUltimateThread;
	private ManualReleaseToolchainJob mCurrentJob;

	private final Semaphore mUltimateExit;
	private final Semaphore mUltimateReady;
	private IToolchainData<RunDefinition> mToolchainData;

	public CDTController(final UltimateCChecker currentChecker) throws Exception {
		mChecker = currentChecker;
		mUltimateExit = new Semaphore(0);
		mUltimateReady = new Semaphore(0);
		initUltimateThread();
	}

	@Override
	public int init(final ICore<RunDefinition> core) {
		// we use init() only to create the preference pages and safe a core
		// reference
		mLogger = core.getCoreLoggingService().getControllerLogger();
		new UltimatePreferencePageFactory(core).createPreferencePages();
		mCore = core;
		// now we wait for the exit command
		mUltimateReady.release();
		mUltimateExit.acquireUninterruptibly();
		return IApplication.EXIT_OK;
	}

	public void runToolchain(final String toolchainPath, final IASTTranslationUnit ast) throws Exception {
		initUltimateThread();
		mLogger.info("Using toolchain " + toolchainPath);
		mToolchainData = mCore.createToolchainData(toolchainPath);
		mChecker.setServices(mToolchainData.getServices());
		mChecker.setStorage(mToolchainData.getStorage());

		mCurrentJob = new ManualReleaseToolchainJob("Run Ultimate...", mCore, this, new WrapperNode(null, ast),
				new ModelType(Activator.PLUGIN_ID, Type.AST, new ArrayList<String>()), mLogger);
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
			final Exception ex = mUltimateThread.getInnerException();
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
	public IToolchainData<RunDefinition> selectTools(final List<ITool> tools) {
		return mToolchainData;
	}

	@Override
	public List<String> selectModel(final List<String> modelNames) {
		final ArrayList<String> returnList = new ArrayList<String>();
		for (final String model : modelNames) {
			if (model.contains(
					de.uni_freiburg.informatik.ultimate.plugins.generator.cacsl2boogietranslator.Activator.PLUGIN_ID)) {
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
	public ISource selectParser(final Collection<ISource> parser) {
		throw new UnsupportedOperationException("This method should never be called for this controller!");
	}

	@Override
	public IPreferenceInitializer getPreferences() {
		// cdt uses the codan preference handling
		return null;
	}

	@Override
	public void displayToolchainResults(final IToolchainData<RunDefinition> toolchain,
			final Map<String, List<IResult>> results) {
		// TODO Auto-generated method stub

	}

	@Override
	public void displayException(final IToolchainData<RunDefinition> toolchain, final String description,
			final Throwable ex) {
		// TODO Auto-generated method stub
	}

	private class UltimateThread {

		private final IController<RunDefinition> mController;
		private Exception mUltimateException;
		private boolean mIsRunning;

		private UltimateThread(final IController<RunDefinition> controller) {
			mController = controller;
		}

		public void startUltimate() {
			final Thread t = new Thread(new Runnable() {
				@Override
				public void run() {
					mIsRunning = true;
					// initialize ultimate core in its own thread, which then
					// delegates control to init and should stay there until
					// close() is called
					final UltimateCore core = new UltimateCore();
					try {
						core.startManually(mController);
					} catch (final Exception e) {
						mUltimateException = e;
					}
					mIsRunning = false;
				}
			}, "CDTUltimateThread");
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

		private IToolchain<RunDefinition> mCurrentChain;

		public ManualReleaseToolchainJob(final String name, final ICore<RunDefinition> core,
				final IController<RunDefinition> controller, final IElement ast, final ModelType outputDefinition,
				final ILogger logger) {
			super(name, core, controller, ast, outputDefinition, logger);
		}

		@Override
		protected void releaseToolchain(final IToolchain<RunDefinition> chain) {
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
