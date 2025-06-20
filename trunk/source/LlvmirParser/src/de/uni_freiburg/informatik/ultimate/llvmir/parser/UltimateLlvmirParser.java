/*
 * Copyright (C) 2025 Peter Ritter
 *
 * This file is part of the ULTIMATE LlvmirParser plug-in.
 *
 * The ULTIMATE LlvmirParser plug-in is free software: you can redistribute it and/or modify
 * it under the terms of the GNU Lesser General Public License as published
 * by the Free Software Foundation, either version 3 of the License, or
 * (at your option) any later version.
 *
 * The ULTIMATE LlvmirParser plug-in is distributed in the hope that it will be useful,
 * but WITHOUT ANY WARRANTY; without even the implied warranty of
 * MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
 * GNU Lesser General Public License for more details.
 *
 * You should have received a copy of the GNU Lesser General Public License
 * along with the ULTIMATE LlvmirParser plug-in. If not, see <http://www.gnu.org/licenses/>.
 *
 * Additional permission under GNU GPL version 3 section 7:
 * If you modify the ULTIMATE LlvmirParser plug-in, or any covered work, by linking
 * or combining it with Eclipse RCP (or a modified version of Eclipse RCP),
 * containing parts covered by the terms of the Eclipse Public License, the
 * licensors of the ULTIMATE LlvmirParser plug-in grant you additional permission
 * to convey the resulting work.
 */
package de.uni_freiburg.informatik.ultimate.llvmir.parser;

import java.io.File;
import java.io.IOException;
import java.util.ArrayList;
import java.util.Arrays;
import java.util.List;
import java.util.stream.Collectors;

import org.antlr.v4.runtime.CharStream;
import org.antlr.v4.runtime.CharStreams;
import org.antlr.v4.runtime.CommonTokenStream;
import org.antlr.v4.runtime.tree.ParseTree;

import de.uni_freiburg.informatik.ultimate.core.model.ISource;
import de.uni_freiburg.informatik.ultimate.core.model.models.IElement;
import de.uni_freiburg.informatik.ultimate.core.model.models.ModelType;
import de.uni_freiburg.informatik.ultimate.core.model.preferences.IPreferenceInitializer;
import de.uni_freiburg.informatik.ultimate.core.model.services.ILogger;
import de.uni_freiburg.informatik.ultimate.core.model.services.IUltimateServiceProvider;
import de.uni_freiburg.informatik.ultimate.lib.llvmir.LLVMIRLexer;
import de.uni_freiburg.informatik.ultimate.lib.llvmir.LLVMIRParser;

public class UltimateLlvmirParser implements ISource {
	protected String[] mFileTypes;
	protected ILogger mLogger;
	protected List<String> mFileNames;
	private IUltimateServiceProvider mServices;

	@Override
	public String getPluginID() {
		return getClass().getPackage().getName();
	}

	@Override
	public void init() {
		mFileTypes = new String[] { ".ll" };
		mFileNames = new ArrayList<>();
	}

	@Override
	public String getPluginName() {
		return "LLVM IR Parser";
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

	/**
	 * Parses a list of files and returns a ParseTree wrapped in an {@link IElement}. For the first implementation, this
	 * method only parses the first file in the list.
	 *
	 * @param files the array of files to be parsed
	 * @return an {@link IElement} representing the ParseTree of the first file
	 * @throws IOException          if an error occurs during file reading or parsing
	 * @throws InterruptedException if the parsing process is interrupted
	 */
	@Override
	public IElement parseAST(final File[] files) throws IOException, InterruptedException {
		if (files == null || files.length == 0) {
			throw new IOException("No files provided for parsing.");
		}
		if (files.length > 1) {
			mLogger.warn("Multiple files provided, only the first one will be parsed.");
		}
		final ParseTree tree = parseFile(files[0]);

		final IElement element = new ParseTreeElementWrapper(tree);
		return element;
	}

	/**
	 * Parses a single file and returns its ParseTree.
	 *
	 * @param file the file to be parsed
	 * @return the ParseTree of the file
	 * @throws IOException          if an error occurs during file reading or parsing
	 * @throws InterruptedException if the parsing process is interrupted
	 */
	private ParseTree parseFile(final File file) throws IOException, InterruptedException {
		mLogger.info("Parsing: '" + file.getAbsolutePath() + "'");
		mFileNames.add(file.getAbsolutePath());
		final LLVMIRParser parser = getParser(getOptFile(file));

		final ParseTree tree = parser.compilationUnit();
		return tree;
	}

	/**
	 * Reads the LLVM IR file and applies optimizations using the LlvmirOptPipeline.
	 *
	 * @param file the file to be optimized
	 * @return a File object representing the optimized LLVM IR file
	 * @throws IOException          if an error occurs while reading or writing the file
	 * @throws InterruptedException if the optimization process is interrupted
	 */
	private static File getOptFile(final File file) throws IOException, InterruptedException {
		return LlvmirOptPipeline.optLlFile(file);
	}

	/**
	 * Creates a new {@link LLVMIRParser} for the given file.
	 *
	 * @param file the file to be parsed
	 * @return a new instance of {@link LLVMIRParser}
	 * @throws IOException if an error occurs while reading the file
	 */
	private static LLVMIRParser getParser(final File file) throws IOException {
		final CharStream input = CharStreams.fromFileName(file.getAbsolutePath());
		final LLVMIRLexer lexer = new LLVMIRLexer(input);
		final CommonTokenStream tokens = new CommonTokenStream(lexer);
		return new LLVMIRParser(tokens);
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

	@Override
	public void setServices(final IUltimateServiceProvider services) {
		mServices = services;
		mLogger = mServices.getLoggingService().getLogger(Activator.PLUGIN_ID);
	}

	@Override
	public void finish() {
		// probably not needed
	}

	@Override
	public IPreferenceInitializer getPreferences() {
		return null;
	}
}
