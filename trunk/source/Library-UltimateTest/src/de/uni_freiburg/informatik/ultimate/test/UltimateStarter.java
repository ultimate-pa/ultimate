/*
 * Copyright (C) 2014-2015 Daniel Dietsch (dietsch@informatik.uni-freiburg.de)
 * Copyright (C) 2015 University of Freiburg
 *
 * This file is part of the ULTIMATE UnitTest Library.
 *
 * The ULTIMATE UnitTest Library is free software: you can redistribute it and/or modify
 * it under the terms of the GNU Lesser General Public License as published
 * by the Free Software Foundation, either version 3 of the License, or
 * (at your option) any later version.
 *
 * The ULTIMATE UnitTest Library is distributed in the hope that it will be useful,
 * but WITHOUT ANY WARRANTY; without even the implied warranty of
 * MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE. See the
 * GNU Lesser General Public License for more details.
 *
 * You should have received a copy of the GNU Lesser General Public License
 * along with the ULTIMATE UnitTest Library. If not, see <http://www.gnu.org/licenses/>.
 *
 * Additional permission under GNU GPL version 3 section 7:
 * If you modify the ULTIMATE UnitTest Library, or any covered work, by linking
 * or combining it with Eclipse RCP (or a modified version of Eclipse RCP),
 * containing parts covered by the terms of the Eclipse Public License, the
 * licensors of the ULTIMATE UnitTest Library grant you additional permission
 * to convey the resulting work.
 */
package de.uni_freiburg.informatik.ultimate.test;

import java.io.FileNotFoundException;
import java.util.Collection;
import java.util.List;
import java.util.Map;

import javax.xml.bind.JAXBException;

import org.eclipse.core.runtime.IStatus;
import org.xml.sax.SAXException;

import de.uni_freiburg.informatik.ultimate.core.coreplugin.external.ExternalUltimateCore;
import de.uni_freiburg.informatik.ultimate.core.lib.toolchain.RunDefinition;
import de.uni_freiburg.informatik.ultimate.core.model.IController;
import de.uni_freiburg.informatik.ultimate.core.model.ICore;
import de.uni_freiburg.informatik.ultimate.core.model.ISource;
import de.uni_freiburg.informatik.ultimate.core.model.ITool;
import de.uni_freiburg.informatik.ultimate.core.model.IToolchainData;
import de.uni_freiburg.informatik.ultimate.core.model.preferences.IPreferenceInitializer;
import de.uni_freiburg.informatik.ultimate.core.model.results.IResult;
import de.uni_freiburg.informatik.ultimate.core.model.services.ILogger;
import de.uni_freiburg.informatik.ultimate.core.model.services.ILoggingService;
import de.uni_freiburg.informatik.ultimate.core.model.services.IUltimateServiceProvider;

/**
 *
 * This class wraps the Ultimate application and allows to start it without setting an IController
 * <ToolchainListType> object.
 *
 * Call runUltimate() to execute it and complete after processing the results (to release resources).
 *
 * @author Daniel Dietsch (dietsch@informatik.uni-freiburg.de)
 *
 */
public class UltimateStarter implements IController<RunDefinition> {

	private ILogger mLogger;

	private final UltimateRunDefinition mUltimateRunDefinition;
	private final long mDeadline;
	private final ExternalUltimateCore mExternalUltimateCore;

	private IUltimateServiceProvider mCurrentSerivces;
	private ILoggingService mLoggingService;

	private ICore<RunDefinition> mCurrentCore;

	public UltimateStarter(final UltimateRunDefinition ultimateRunDefinition, final long deadline) {
		assert deadline >= 0 : "Deadline has to be positive or zero";
		mUltimateRunDefinition = ultimateRunDefinition;
		mExternalUltimateCore = new ExternalUltimateCore(this);
		mDeadline = deadline;
	}

	public IStatus runUltimate() throws Throwable {
		return mExternalUltimateCore.runUltimate();
	}

	@Override
	public int init(final ICore<RunDefinition> core) {
		mLoggingService = core.getCoreLoggingService();
		mLogger = mLoggingService.getControllerLogger();
		mCurrentCore = core;
		core.resetPreferences();
		return mExternalUltimateCore
				.init(core, mUltimateRunDefinition.getSettings(), mDeadline, mUltimateRunDefinition.getInput())
				.getCode();
	}

	public void complete() {
		mExternalUltimateCore.complete();
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
	public IPreferenceInitializer getPreferences() {
		return null;
	}

	@Override
	public ISource selectParser(final Collection<ISource> parser) {
		mLogger.fatal("UltimateStarter does not support the selection of parsers by the user!");
		return null;
	}

	@Override
	public IToolchainData<RunDefinition> selectTools(final List<ITool> tools) {
		try {
			final IToolchainData<RunDefinition> tc =
					mCurrentCore.createToolchainData(mUltimateRunDefinition.getToolchain().getAbsolutePath());
			mCurrentSerivces = tc.getServices();
			mLogger.info("Loaded toolchain from " + mUltimateRunDefinition.getToolchain().getAbsolutePath());
			return tc;
		} catch (FileNotFoundException | JAXBException | SAXException e) {
			mLogger.fatal(
					"Toolchain could not be created from file " + mUltimateRunDefinition.getToolchain() + ": " + e);
			return null;
		}
	}

	@Override
	public List<String> selectModel(final List<String> modelNames) {
		mLogger.fatal("UltimateStarter does not support the selection of models by the user!");
		return null;
	}

	@Override
	public void displayToolchainResults(final IToolchainData<RunDefinition> toolchain,
			final Map<String, List<IResult>> results) {

	}

	@Override
	public void displayException(final IToolchainData<RunDefinition> toolchain, final String description,
			final Throwable ex) {
		mLogger.fatal("Exception during Ultimate run: ", ex);

	}

	/**
	 * Provides an {@link IUltimateServiceProvider} instance of the last run of this starter (i.e., only after
	 * {@link #runUltimate()} has been called).
	 */
	public IUltimateServiceProvider getServices() {
		return mCurrentSerivces;
	}

	@Override
	public void prerun(final IToolchainData<RunDefinition> tcData) {

	}
}
