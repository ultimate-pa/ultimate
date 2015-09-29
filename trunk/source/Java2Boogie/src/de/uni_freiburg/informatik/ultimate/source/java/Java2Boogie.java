/*
 * Copyright (C) 2015 Daniel Dietsch (dietsch@informatik.uni-freiburg.de)
 * Copyright (C) 2015 University of Freiburg
 * 
 * This file is part of the ULTIMATE Java2Boogie plug-in.
 * 
 * The ULTIMATE Java2Boogie plug-in is free software: you can redistribute it and/or modify
 * it under the terms of the GNU Lesser General Public License as published
 * by the Free Software Foundation, either version 3 of the License, or
 * (at your option) any later version.
 * 
 * The ULTIMATE Java2Boogie plug-in is distributed in the hope that it will be useful,
 * but WITHOUT ANY WARRANTY; without even the implied warranty of
 * MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
 * GNU Lesser General Public License for more details.
 * 
 * You should have received a copy of the GNU Lesser General Public License
 * along with the ULTIMATE Java2Boogie plug-in. If not, see <http://www.gnu.org/licenses/>.
 * 
 * Additional permission under GNU GPL version 3 section 7:
 * If you modify the ULTIMATE Java2Boogie plug-in, or any covered work, by linking
 * or combining it with Eclipse RCP (or a modified version of Eclipse RCP), 
 * containing parts covered by the terms of the Eclipse Public License, the 
 * licensors of the ULTIMATE Java2Boogie plug-in grant you additional permission 
 * to convey the resulting work.
 */

package de.uni_freiburg.informatik.ultimate.source.java;

import java.io.File;
import java.io.IOException;
import java.util.ArrayList;
import java.util.List;

import org.apache.log4j.Level;
import org.apache.log4j.Logger;
import org.joogie.Dispatcher;
import org.joogie.HeapMode;
import org.joogie.boogie.BoogieProgram;

import de.uni_freiburg.informatik.ultimate.core.preferences.UltimatePreferenceInitializer;
import de.uni_freiburg.informatik.ultimate.core.services.IToolchainStorage;
import de.uni_freiburg.informatik.ultimate.core.services.IUltimateServiceProvider;
import de.uni_freiburg.informatik.ultimate.ep.interfaces.ISource;
import de.uni_freiburg.informatik.ultimate.model.GraphType;
import de.uni_freiburg.informatik.ultimate.model.IElement;
import de.uni_freiburg.informatik.ultimate.model.Payload;
import de.uni_freiburg.informatik.ultimate.model.boogie.ast.Unit;
import de.uni_freiburg.informatik.ultimate.model.structure.WrapperNode;

/**
 * 
 * @author Daniel Dietsch (dietsch@informatik.uni-freiburg.de)
 *
 */
public final class Java2Boogie implements ISource {
	private final String[] mFileTypes;

	private List<String> mFileNames;
	private Logger mLogger;
	private IUltimateServiceProvider mServices;

	public Java2Boogie() {
		mFileTypes = new String[] { "class", "java", "jar" };
		mFileNames = new ArrayList<String>();
	}

	@Override
	public String getPluginID() {
		return getClass().getPackage().getName();
	}

	@Override
	public void init() {
		mFileNames = new ArrayList<String>();
	}

	@Override
	public String getPluginName() {
		return "Java2Boogie";
	}

	@Override
	public IElement parseAST(final File[] files) throws IOException {
		final WrapperNode dirRoot = new WrapperNode(null, null, new Payload(null, "PROJECT"));

		for (final File file : files) {
			Unit node = (Unit) parseAST(file);
			dirRoot.addOutgoing(new WrapperNode(dirRoot, node));
		}
		return dirRoot;
	}

	@Override
	public IElement parseAST(final File file) throws IOException {
		final Dispatcher dispatch = new Dispatcher(file.getAbsolutePath(), HeapMode.Default, null, null, mLogger);
		final BoogieProgram boogieprog = dispatch.run();
		return new Joogie2BoogieTranslator(boogieprog, mServices, file.getAbsolutePath()).getUnit();
	}

	@Override
	public boolean parseable(File[] files) {
		for (final File f : files) {
			if (!parseable(f)) {
				return false;
			}
		}
		return true;
	}

	@Override
	public boolean parseable(File file) {
		for (final String ending : getFileTypes()) {
			if (file.getName().endsWith(ending))
				return true;
		}
		return false;
	}

	@Override
	public String[] getFileTypes() {
		return mFileTypes;
	}

	@Override
	public GraphType getOutputDefinition() {
		try {
			return new GraphType(getPluginID(), GraphType.Type.AST, mFileNames);
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
	public void setToolchainStorage(IToolchainStorage services) {

	}

	@Override
	public void setServices(IUltimateServiceProvider services) {
		mServices = services;
		mLogger = mServices.getLoggingService().getLogger(Activator.PLUGIN_ID);
	}

	@Override
	public void finish() {

	}
}
