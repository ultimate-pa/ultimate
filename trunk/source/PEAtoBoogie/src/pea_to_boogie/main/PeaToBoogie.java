/*
 * Copyright (C) 2013-2015 Daniel Dietsch (dietsch@informatik.uni-freiburg.de)
 * Copyright (C) 2013-2015 Jochen Hoenicke (hoenicke@informatik.uni-freiburg.de)
 * Copyright (C) 2015 University of Freiburg
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
package pea_to_boogie.main;

import java.io.File;
import java.util.ArrayList;
import java.util.BitSet;
import java.util.List;

import org.apache.log4j.Level;
import org.apache.log4j.Logger;

import pea_to_boogie.Activator;
import pea_to_boogie.translator.Translator;
import req_to_pea.ReqToPEA;
import srParse.srParsePattern;
import de.uni_freiburg.informatik.ultimate.core.preferences.UltimatePreferenceInitializer;
import de.uni_freiburg.informatik.ultimate.core.services.model.IToolchainStorage;
import de.uni_freiburg.informatik.ultimate.core.services.model.IUltimateServiceProvider;
import de.uni_freiburg.informatik.ultimate.ep.interfaces.ISource;
import de.uni_freiburg.informatik.ultimate.model.ModelType;
import de.uni_freiburg.informatik.ultimate.model.IElement;

public class PeaToBoogie implements ISource {
	protected Logger mLogger;
	List<String> mFileNames = new ArrayList<String>();

	@Override
	public void init() {
	}

	@Override
	public String getPluginName() {
		return "PEA to Boogie";
	}

	@Override
	public String getPluginID() {
		return Activator.s_PLUGIN_ID;
	}

	@Override
	public boolean parseable(File[] files) {
		return false;
	}

	@Override
	public boolean parseable(File file) {
		return file.getName().endsWith(".req");
	}

	@Override
	public IElement parseAST(File[] files) throws Exception {
		throw new UnsupportedOperationException();
	}

	@Override
	public IElement parseAST(File file) throws Exception {
		Translator translator = new Translator();
		String inputPath = file.getAbsolutePath();
		mFileNames = new ArrayList<String>();
		mFileNames.add(inputPath);
		mLogger.info("Parsing: '" + inputPath + "'");
		srParsePattern[] patterns = new ReqToPEA().genPatterns(inputPath);
		//TODO: Add options to this cruel program 
		BitSet vacuityChecks = new BitSet(patterns.length);
		vacuityChecks.set(0, patterns.length);
		
		int combinationNum = Math.min(patterns.length, 2); // TODO preference
		translator.setVacuityChecks(vacuityChecks);
		translator.setCombinationNum(combinationNum);
		translator.setInputFilePath(inputPath);
		return translator.genBoogie(patterns);
	}

	@Override
	public String[] getFileTypes() {
		return new String[] { ".req" };
	}

	@Override
	public ModelType getOutputDefinition() {
		try {
			return new ModelType(getPluginID(), ModelType.Type.AST, mFileNames);
		} catch (Exception ex) {
			mLogger.log(Level.FATAL, "syntax error: " + ex.getMessage());
			return null;
		}
	}

	@Override
	public void setPreludeFile(File prelude) {

	}

	@Override
	public UltimatePreferenceInitializer getPreferences() {
		return null;
	}

	@Override
	public void setToolchainStorage(IToolchainStorage storage) {
		// TODO Auto-generated method stub

	}

	@Override
	public void setServices(IUltimateServiceProvider services) {
		mLogger = services.getLoggingService().getLogger(Activator.s_PLUGIN_ID);
	}

	@Override
	public void finish() {
		
	}
}
