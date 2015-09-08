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
import java.util.Collections;

import de.uni_freiburg.informatik.ultimate.core.preferences.UltimatePreferenceInitializer;
import de.uni_freiburg.informatik.ultimate.core.services.IToolchainStorage;
import de.uni_freiburg.informatik.ultimate.core.services.IUltimateServiceProvider;
import de.uni_freiburg.informatik.ultimate.ep.interfaces.ISource;
import de.uni_freiburg.informatik.ultimate.model.GraphType;
import de.uni_freiburg.informatik.ultimate.model.GraphType.Type;
import de.uni_freiburg.informatik.ultimate.model.IElement;

/**
 * @author dietsch@informatik.uni-freiburg.de
 * 
 */
public class WitnessParser implements ISource {

	private static final String[] sFileTypes = new String[] { "graphml" };
	private IUltimateServiceProvider mServices;
	private String mFilename;

	@Override
	public void setToolchainStorage(IToolchainStorage storage) {
		// TODO Auto-generated method stub

	}

	@Override
	public void setServices(IUltimateServiceProvider services) {
		mServices = services;
	}

	@Override
	public void init() {

	}

	@Override
	public void finish() {

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
	public UltimatePreferenceInitializer getPreferences() {
		return null;
	}

	@Override
	public boolean parseable(File[] files) {
		if (files != null && files.length == 1) {
			return parseable(files[0]);
		}
		return false;
	}

	@Override
	public boolean parseable(File file) {
		if (file != null && file.exists() && file.isFile()) {
			for (String suffix : getFileTypes()) {
				if (file.getName().endsWith(suffix)) {
					return true;
				}
			}
		}
		return false;
	}

	@Override
	public IElement parseAST(File[] files) throws Exception {
		if (files == null || files.length != 1) {
			throw new UnsupportedOperationException("We currently do not support multiple witnesses");
		}
		return parseAST(files[0]);
	}

	@Override
	public IElement parseAST(File file) throws Exception {
		mFilename = file.getAbsolutePath();
		return new WitnessAutomatonConstructor(mServices).constructWitnessAutomaton(file);
	}

	@Override
	public String[] getFileTypes() {
		return sFileTypes;
	}

	@Override
	public GraphType getOutputDefinition() {
		return new GraphType(getPluginID(), Type.OTHER, Collections.singleton(mFilename));
	}

	@Override
	public void setPreludeFile(File prelude) {

	}

}
