/*
 * Copyright (C) 2013-2018 Daniel Dietsch (dietsch@informatik.uni-freiburg.de)
 * Copyright (C) 2013-2015 Jochen Hoenicke (hoenicke@informatik.uni-freiburg.de)
 * Copyright (C) 2013-2018 University of Freiburg
 *
 * This file is part of the ULTIMATE PEAtoBoogie plug-in.
 *
 * The ULTIMATE PEAtoBoogie plug-in is free software: you can redistribute it and/or modify
 * it under the terms of the GNU Lesser General Public License as published
 * by the Free Software Foundation, either version 3 of the License, or
 * (at your option) any later version.
 *
 * The ULTIMATE PEAtoBoogie plug-in is distributed in the hope that it will be useful,
 * but WITHOUT ANY WARRANTY; without even the implied warranty of
 * MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE. See the
 * GNU Lesser General Public License for more details.
 *
 * You should have received a copy of the GNU Lesser General Public License
 * along with the ULTIMATE PEAtoBoogie plug-in. If not, see <http://www.gnu.org/licenses/>.
 *
 * Additional permission under GNU GPL version 3 section 7:
 * If you modify the ULTIMATE PEAtoBoogie plug-in, or any covered work, by linking
 * or combining it with Eclipse RCP (or a modified version of Eclipse RCP),
 * containing parts covered by the terms of the Eclipse Public License, the
 * licensors of the ULTIMATE PEAtoBoogie plug-in grant you additional permission
 * to convey the resulting work.
 */
package de.uni_freiburg.informatik.ultimate.reqparser;

import java.io.File;
import java.io.FileInputStream;
import java.util.ArrayList;
import java.util.Arrays;
import java.util.List;
import java.util.stream.Collectors;

import com.github.jhoenicke.javacup.runtime.Symbol;

import de.uni_freiburg.informatik.ultimate.core.lib.models.ObjectContainer;
import de.uni_freiburg.informatik.ultimate.core.lib.models.annotation.DefaultLocation;
import de.uni_freiburg.informatik.ultimate.core.model.ISource;
import de.uni_freiburg.informatik.ultimate.core.model.models.IElement;
import de.uni_freiburg.informatik.ultimate.core.model.models.ModelType;
import de.uni_freiburg.informatik.ultimate.core.model.preferences.IPreferenceInitializer;
import de.uni_freiburg.informatik.ultimate.core.model.services.ILogger;
import de.uni_freiburg.informatik.ultimate.core.model.services.IToolchainStorage;
import de.uni_freiburg.informatik.ultimate.core.model.services.IUltimateServiceProvider;
import de.uni_freiburg.informatik.ultimate.lib.srparse.pattern.PatternType;

public class ReqParser implements ISource {
	private ILogger mLogger;
	private List<String> mFileNames = new ArrayList<>();
	private IUltimateServiceProvider mServices;
	private IToolchainStorage mStorage;

	@Override
	public void init() {
		// not necessary
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
	public File[] parseable(final File[] files) {
		final List<File> rtrList = Arrays.stream(files).filter(this::parseable).collect(Collectors.toList());
		return rtrList.toArray(new File[rtrList.size()]);
	}

	public boolean parseable(final File file) {
		return file.getName().endsWith(".req");
	}

	@Override
	public IElement parseAST(final File[] files) throws Exception {
		final List<PatternType> rawPatterns = new ArrayList<>();
		for (File file: files) {
			final FileInputStream fis = new FileInputStream(file);
			mLogger.info("Parsing file "+file.getName());
			try {
				final de.uni_freiburg.informatik.ultimate.lib.srparse.ReqParser parser 
				= new de.uni_freiburg.informatik.ultimate.lib.srparse.ReqParser(mServices, mLogger, fis, file.getName());
				final Symbol goal = parser.parse();
				rawPatterns.addAll(Arrays.asList((PatternType[]) goal.value));
			} finally {
				mLogger.error("Error in file: "+file.getName());
				fis.close();
			}
		}
		return new ObjectContainer<List<PatternType>>(rawPatterns);
	}

	@Override
	public String[] getFileTypes() {
		return new String[] { ".req" };
	}

	@Override
	public ModelType getOutputDefinition() {
		try {
			return new ModelType(getPluginID(), ModelType.Type.OTHER, mFileNames);
		} catch (final Exception ex) {
			mLogger.fatal("syntax error: " + ex.getMessage());
			return null;
		}
	}

	@Override
	public void setToolchainStorage(final IToolchainStorage storage) {
		mStorage = storage;
	}

	@Override
	public void setServices(final IUltimateServiceProvider services) {
		mServices = services;
		mLogger = services.getLoggingService().getLogger(Activator.PLUGIN_ID);
		//mReporter = new PeaResultUtil(mLogger, mServices);
	}

	@Override
	public void finish() {
		// not necessary
	}

	@Override
	public IPreferenceInitializer getPreferences() {
		// TODO Auto-generated method stub
		return null;
	}

}
