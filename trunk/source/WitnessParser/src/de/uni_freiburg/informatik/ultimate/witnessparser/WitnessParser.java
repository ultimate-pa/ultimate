/*
 * Copyright (C) 2015 Daniel Dietsch (dietsch@informatik.uni-freiburg.de)
 * Copyright (C) 2015 University of Freiburg
 *
 * This file is part of the ULTIMATE WitnessParser plug-in.
 *
 * The ULTIMATE WitnessParser plug-in is free software: you can redistribute it and/or modify
 * it under the terms of the GNU Lesser General Public License as published
 * by the Free Software Foundation, either version 3 of the License, or
 * (at your option) any later version.
 *
 * The ULTIMATE WitnessParser plug-in is distributed in the hope that it will be useful,
 * but WITHOUT ANY WARRANTY; without even the implied warranty of
 * MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE. See the
 * GNU Lesser General Public License for more details.
 *
 * You should have received a copy of the GNU Lesser General Public License
 * along with the ULTIMATE WitnessParser plug-in. If not, see <http://www.gnu.org/licenses/>.
 *
 * Additional permission under GNU GPL version 3 section 7:
 * If you modify the ULTIMATE WitnessParser plug-in, or any covered work, by linking
 * or combining it with Eclipse RCP (or a modified version of Eclipse RCP),
 * containing parts covered by the terms of the Eclipse Public License, the
 * licensors of the ULTIMATE WitnessParser plug-in grant you additional permission
 * to convey the resulting work.
 */
package de.uni_freiburg.informatik.ultimate.witnessparser;

import java.io.File;
import java.io.FileNotFoundException;
import java.util.Collections;

import de.uni_freiburg.informatik.ultimate.core.lib.results.InvalidWitnessErrorResult;
import de.uni_freiburg.informatik.ultimate.core.lib.results.InvalidWitnessErrorResult.InvalidWitnessReasons;
import de.uni_freiburg.informatik.ultimate.core.model.ISource;
import de.uni_freiburg.informatik.ultimate.core.model.models.IElement;
import de.uni_freiburg.informatik.ultimate.core.model.models.ModelType;
import de.uni_freiburg.informatik.ultimate.core.model.models.ModelType.Type;
import de.uni_freiburg.informatik.ultimate.core.model.preferences.IPreferenceInitializer;
import de.uni_freiburg.informatik.ultimate.core.model.services.ILogger;
import de.uni_freiburg.informatik.ultimate.core.model.services.IToolchainStorage;
import de.uni_freiburg.informatik.ultimate.core.model.services.IUltimateServiceProvider;
import de.uni_freiburg.informatik.ultimate.witnessparser.preferences.WitnessParserPreferences;
import edu.uci.ics.jung.io.GraphIOException;

/**
 * @author Daniel Dietsch (dietsch@informatik.uni-freiburg.de)
 *
 */
public class WitnessParser implements ISource {

	private static final String[] FILE_TYPES = new String[] { "graphml" };
	private IUltimateServiceProvider mServices;
	private String mFilename;
	private ModelType.Type mWitnessType;
	private ILogger mLogger;

	@Override
	public void setToolchainStorage(final IToolchainStorage storage) {
		// no toolchainstorage needed
	}

	@Override
	public void setServices(final IUltimateServiceProvider services) {
		mServices = services;
		mLogger = services.getLoggingService().getLogger(Activator.PLUGIN_ID);
	}

	@Override
	public void init() {
		// no init necessary
	}

	@Override
	public void finish() {
		// no finish necessary
	}

	@Override
	public String getPluginName() {
		return Activator.PLUGIN_NAME;
	}

	@Override
	public String getPluginID() {
		return Activator.PLUGIN_ID;
	}

	@Override
	public IPreferenceInitializer getPreferences() {
		return new WitnessParserPreferences();
	}

	@Override
	public boolean parseable(final File[] files) {
		if (files != null && files.length == 1) {
			return parseable(files[0]);
		}
		return false;
	}

	@Override
	public boolean parseable(final File file) {
		for (final String suffix : getFileTypes()) {
			if (file.getName().endsWith(suffix)) {
				return true;
			}
		}
		return false;
	}

	@Override
	public IElement parseAST(final File[] files) throws Exception {
		if (files == null || files.length != 1) {
			throw new UnsupportedOperationException("We currently do not support multiple witnesses");
		}
		return parseAST(files[0]);
	}

	@Override
	public IElement parseAST(final File file) {
		mFilename = file.getAbsolutePath();
		final WitnessAutomatonConstructor wac = new WitnessAutomatonConstructor(mServices);
		try {
			final IElement rtr = wac.constructWitnessAutomaton(file);
			mWitnessType = wac.getWitnessType();
			return rtr;
		} catch (final FileNotFoundException e) {
			reportInvalidWitnessResult(e.getMessage(), InvalidWitnessReasons.FILE_NOT_FOUND);
		} catch (final GraphIOException e) {
			reportInvalidWitnessResult(e.getMessage(), InvalidWitnessReasons.XML_INVALID);
		}
		mWitnessType = Type.OTHER;
		return null;
	}

	@Override
	public String[] getFileTypes() {
		return FILE_TYPES;
	}

	@Override
	public ModelType getOutputDefinition() {
		return new ModelType(getPluginID(), mWitnessType, Collections.singleton(mFilename));
	}

	@Override
	public void setPreludeFile(final File prelude) {
		// no prelude necessary
	}

	/**
	 * Report an invalid witness to Ultimate. This will cancel the toolchain.
	 * 
	 * @param msg
	 *            A more detailed reason .
	 * @param reason
	 *            The reason for invalidity.
	 */
	public void reportInvalidWitnessResult(final String msg, final InvalidWitnessReasons reason) {
		final InvalidWitnessErrorResult result = new InvalidWitnessErrorResult(Activator.PLUGIN_ID, reason, msg);
		mLogger.error(msg);
		mServices.getResultService().reportResult(Activator.PLUGIN_ID, result);
		mServices.getProgressMonitorService().cancelToolchain();
	}
}
