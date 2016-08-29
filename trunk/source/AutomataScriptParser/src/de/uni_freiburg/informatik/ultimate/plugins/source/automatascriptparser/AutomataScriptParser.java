/*
 * Copyright (C) 2013-2015 Betim Musa (musab@informatik.uni-freiburg.de)
 * Copyright (C) 2013-2015 Daniel Dietsch (dietsch@informatik.uni-freiburg.de)
 * Copyright (C) 2012-2015 Matthias Heizmann (heizmann@informatik.uni-freiburg.de)
 * Copyright (C) 2015 University of Freiburg
 * 
 * This file is part of the ULTIMATE AutomataScriptParser plug-in.
 * 
 * The ULTIMATE AutomataScriptParser plug-in is free software: you can redistribute it and/or modify
 * it under the terms of the GNU Lesser General Public License as published
 * by the Free Software Foundation, either version 3 of the License, or
 * (at your option) any later version.
 * 
 * The ULTIMATE AutomataScriptParser plug-in is distributed in the hope that it will be useful,
 * but WITHOUT ANY WARRANTY; without even the implied warranty of
 * MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
 * GNU Lesser General Public License for more details.
 * 
 * You should have received a copy of the GNU Lesser General Public License
 * along with the ULTIMATE AutomataScriptParser plug-in. If not, see <http://www.gnu.org/licenses/>.
 * 
 * Additional permission under GNU GPL version 3 section 7:
 * If you modify the ULTIMATE AutomataScriptParser plug-in, or any covered work, by linking
 * or combining it with Eclipse RCP (or a modified version of Eclipse RCP), 
 * containing parts covered by the terms of the Eclipse Public License, the 
 * licensors of the ULTIMATE AutomataScriptParser plug-in grant you additional permission 
 * to convey the resulting work.
 */
package de.uni_freiburg.informatik.ultimate.plugins.source.automatascriptparser;

import java.io.File;
import java.io.FileReader;
import java.io.Reader;
import java.util.ArrayList;
import java.util.List;

import de.uni_freiburg.informatik.ultimate.core.model.ISource;
import de.uni_freiburg.informatik.ultimate.core.model.models.IElement;
import de.uni_freiburg.informatik.ultimate.core.model.models.ModelType;
import de.uni_freiburg.informatik.ultimate.core.model.preferences.IPreferenceInitializer;
import de.uni_freiburg.informatik.ultimate.core.model.services.ILogger;
import de.uni_freiburg.informatik.ultimate.core.model.services.IToolchainStorage;
import de.uni_freiburg.informatik.ultimate.core.model.services.IUltimateServiceProvider;

public class AutomataScriptParser implements ISource {

	protected String[] mFileTypes = new String[] { "ats" };

	protected List<String> mFileNames = new ArrayList<String>();

	private ILogger mLogger;

	private IUltimateServiceProvider mServices;

	private IElement parseFile(final File file) throws Exception {
		
		final Reader reader = new FileReader(file);
		final String filename = file.getName();
		final String fileAbsolutePath = file.getAbsolutePath();
		
		return (new AutomataScriptParserRun(mServices, mLogger, reader, filename, fileAbsolutePath)).getResult();
	}

	@Override
	public String[] getFileTypes() {
		return mFileTypes;
	}

	@Override
	public ModelType getOutputDefinition() {
		try {
			return new ModelType(getPluginID(), ModelType.Type.AST, mFileNames);
		} catch (final Exception ex) {
			mLogger.fatal(ex.getMessage());
			return null;
		}
	}

	@Override
	public IElement parseAST(final File[] files) throws Exception {
		mLogger.warn("AutomataScriptParser can not parse more than one file. Parsing only " + files[0].getName()
				+ "and ignoring the other input files");
		return parseAST(files[0]);
	}

	@Override
	public IElement parseAST(final File file) throws Exception {
		mFileNames.add(file.getName());
		mLogger.info("Parsing '" + file.getAbsolutePath() + "'");
		return parseFile(file);
	}

	@Override
	public boolean parseable(final File[] files) {
		for (final File f : files) {
			if (!parseable(f)) {
				return false;
			}
		}
		return true;
	}

	@Override
	public boolean parseable(final File file) {
		for (final String s : getFileTypes()) {
			if (file.getName().endsWith(s)) {
				return true;
			}
		}
		return false;
	}

	@Override
	public void setPreludeFile(final File prelude) {
		// TODO Auto-generated method stub

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
	public void init() {
	}

	@Override
	public IPreferenceInitializer getPreferences() {
		// TODO Auto-generated method stub
		return null;
	}

	@Override
	public void setToolchainStorage(final IToolchainStorage storage) {

	}

	@Override
	public void setServices(final IUltimateServiceProvider services) {
		mServices = services;
		mLogger = mServices.getLoggingService().getLogger(Activator.PLUGIN_ID);
	}

	@Override
	public void finish() {
		// TODO Auto-generated method stub
		
	}

}
