/*
 * Copyright (C) 2013-2015 Daniel Dietsch (dietsch@informatik.uni-freiburg.de)
 * Copyright (C) 2008-2015 Jochen Hoenicke (hoenicke@informatik.uni-freiburg.de)
 * Copyright (C) 2015 University of Freiburg
 *
 * This file is part of the ULTIMATE BoogiePLParser plug-in.
 *
 * The ULTIMATE BoogiePLParser plug-in is free software: you can redistribute it and/or modify
 * it under the terms of the GNU Lesser General Public License as published
 * by the Free Software Foundation, either version 3 of the License, or
 * (at your option) any later version.
 *
 * The ULTIMATE BoogiePLParser plug-in is distributed in the hope that it will be useful,
 * but WITHOUT ANY WARRANTY; without even the implied warranty of
 * MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
 * GNU Lesser General Public License for more details.
 *
 * You should have received a copy of the GNU Lesser General Public License
 * along with the ULTIMATE BoogiePLParser plug-in. If not, see <http://www.gnu.org/licenses/>.
 *
 * Additional permission under GNU GPL version 3 section 7:
 * If you modify the ULTIMATE BoogiePLParser plug-in, or any covered work, by linking
 * or combining it with Eclipse RCP (or a modified version of Eclipse RCP),
 * containing parts covered by the terms of the Eclipse Public License, the
 * licensors of the ULTIMATE BoogiePLParser plug-in grant you additional permission
 * to convey the resulting work.
 */
package de.uni_freiburg.informatik.ultimate.boogie.parser;

import java.io.File;
import java.io.FileInputStream;
import java.io.IOException;
import java.util.ArrayList;
import java.util.Arrays;
import java.util.List;
import java.util.stream.Collectors;

import de.uni_freiburg.informatik.ultimate.boogie.ast.Unit;
import de.uni_freiburg.informatik.ultimate.core.lib.models.WrapperNode;
import de.uni_freiburg.informatik.ultimate.core.model.ISource;
import de.uni_freiburg.informatik.ultimate.core.model.models.IElement;
import de.uni_freiburg.informatik.ultimate.core.model.models.ModelType;
import de.uni_freiburg.informatik.ultimate.core.model.preferences.IPreferenceInitializer;
import de.uni_freiburg.informatik.ultimate.core.model.services.ILogger;
import de.uni_freiburg.informatik.ultimate.core.model.services.IToolchainStorage;
import de.uni_freiburg.informatik.ultimate.core.model.services.IUltimateServiceProvider;

/**
 * This is the main Boogie 2 parser class that creates the lexer and parser to parse Boogie 2 files into a CST.
 *
 * @author hoenicke
 * @author Daniel Dietsch (dietsch@informatik.uni-freiburg.de)
 *
 */
public class BoogieParser implements ISource {
	protected String[] mFileTypes;
	protected ILogger mLogger;
	protected List<String> mFileNames;
	protected Unit mPreludeUnit;
	private IUltimateServiceProvider mServices;

	public BoogieParser() {
		mFileTypes = new String[] { "bpl" };
		mFileNames = new ArrayList<>();
	}

	@Override
	public String getPluginID() {
		return getClass().getPackage().getName();
	}

	@Override
	public void init() {
		mFileNames = new ArrayList<>();
	}

	@Override
	public String getPluginName() {
		return "Boogie PL CUP Parser";
	}

	/**
	 * Parses a list of files and constructs a tree with root node "PROJECT" if there are multiple files. This function
	 * uses reflection to get the parser, so make sure you set the correct one in your parser.
	 *
	 * @param files
	 *            an array of files to be parsed
	 * @return the tree
	 * @see de.uni_freiburg.informatik.ultimate.ep.interfaces.IParser#parseAST(java.io.File[])
	 */
	@Override
	public IElement parseAST(final File[] files) throws IOException {
		if (files.length > 1) {
			final WrapperNode dirRoot = new WrapperNode(null, null);

			for (final File f : files) {
				final Unit node = parseFile(f);
				dirRoot.addOutgoing(new WrapperNode(dirRoot, node));
			}
			return dirRoot;
		}

		final File file = files[0];
		if (file.isDirectory()) {
			return parseAST(file.listFiles());
		}
		return parseFile(file);
	}

	private Unit parseFile(final File file) throws IOException {
		mLogger.info("Parsing: '" + file.getAbsolutePath() + "'");
		mFileNames.add(file.getAbsolutePath());
		return reflectiveParse(file.getAbsolutePath());
	}

	@Override
	public File[] parseable(final File[] files) {
		final List<File> rtrList = Arrays.stream(files).filter(this::parseable).collect(Collectors.toList());
		return rtrList.toArray(new File[rtrList.size()]);
	}

	private boolean parseable(final File file) {
		for (final String s : getFileTypes()) {
			if (file.getName().endsWith(s)) {
				return true;
			}
		}
		return false;
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
			mLogger.fatal("syntax error: " + ex.getMessage());
			return null;
		}
	}

	/**
	 * This function parses the file given as argument. It is quite flexible so be careful using it
	 *
	 * @param fileName
	 *            the file to be parsed
	 * @return an INode containing the AST
	 */
	private Unit reflectiveParse(final String fileName) throws IOException {
		final BoogieSymbolFactory symFactory = new BoogieSymbolFactory();
		final Lexer lexer = new Lexer(new FileInputStream(fileName));
		lexer.setSymbolFactory(symFactory);
		final Parser parser = new Parser(lexer, symFactory, mServices);
		parser.setFileName(fileName);
		try {
			return (Unit) parser.parse().value;
		} catch (final Exception e) {
			mLogger.fatal("syntax error: ", e);
			throw new RuntimeException(e);
		}
	}

	@Override
	public IPreferenceInitializer getPreferences() {
		return null;
	}

	@Override
	public void setToolchainStorage(final IToolchainStorage services) {
		// not needed
	}

	@Override
	public void setServices(final IUltimateServiceProvider services) {
		mServices = services;
		mLogger = mServices.getLoggingService().getLogger(Activator.PLUGIN_ID);
	}

	@Override
	public void finish() {
		// not needed
	}
}
