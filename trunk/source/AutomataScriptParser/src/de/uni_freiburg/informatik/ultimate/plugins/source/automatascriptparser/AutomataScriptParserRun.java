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
import java.io.FileNotFoundException;
import java.io.FileReader;
import java.io.Reader;
import java.util.ArrayList;
import java.util.List;

import javax.print.attribute.standard.Severity;

import de.uni_freiburg.informatik.ultimate.core.lib.results.SyntaxErrorResult;
import de.uni_freiburg.informatik.ultimate.core.model.models.ILocation;
import de.uni_freiburg.informatik.ultimate.core.model.services.ILogger;
import de.uni_freiburg.informatik.ultimate.core.model.services.IUltimateServiceProvider;
import de.uni_freiburg.informatik.ultimate.plugins.source.automatascriptparser.AST.AutomataDefinitionsAST;
import de.uni_freiburg.informatik.ultimate.plugins.source.automatascriptparser.AST.AutomataTestFileAST;
import de.uni_freiburg.informatik.ultimate.plugins.source.automatascriptparser.AST.AutomatonAST;

public class AutomataScriptParserRun {

	private final IUltimateServiceProvider mServices;
	private final ILogger mLogger;
	private final Reader mReader;
	private final String mFilename;
	private final String mFileAbsolutePath;
	private final AutomataTestFileAST mResult;
	
	public AutomataScriptParserRun(final IUltimateServiceProvider services, final ILogger logger, final Reader reader, final String filename,
			final String fileAbsolutePath) {
		super();
		mServices = services;
		mLogger = logger;
		mReader = reader;
		mFilename = filename;
		mFileAbsolutePath = fileAbsolutePath;
		mResult = doParse(mReader, mFilename, mFileAbsolutePath);
	}

	private AutomataTestFileAST doParse(final Reader reader, final String filename, final String fileAbsolutePath) {
		final Lexer lexer = new Lexer(reader);
		final Parser parser = new Parser(lexer, mLogger);
		parser.setFileName(filename);
		parser.setFilePath(fileAbsolutePath);

		Object result = null;
		try {
			result = parser.parse().value;
		} catch (final Exception e) {
			ILocation location = parser.getErrorLocation();
			if (location == null) {
				mLogger.debug("Error without location");
				location = getPseudoLocation();
			}
			String shortErrorMessage = parser.getShortErrorMessage();
			if (shortErrorMessage == null) {
				shortErrorMessage = e.getMessage();
			}
			String longErrorMessage = parser.getLongErrorMessage();
			if (longErrorMessage == null) {
				longErrorMessage = e.getMessage();
			}
			reportSyntaxError(Severity.ERROR, longErrorMessage, shortErrorMessage, location);
			mLogger.info("Parsing aborted.");
			return null;
		}

		mLogger.debug("'" + filename + "' successfully parsed");
		if (result instanceof AutomataTestFileAST) {
			final AutomataTestFileAST ats = (AutomataTestFileAST) result;
			final AutomataDefinitionsAST autDefs = ats.getAutomataDefinitions();
			// parser contains files to parse, if the operation
			// parseAutomata(pathToFile) was called at least
			// once.
			if (parser.containsOtherAutomataFilesToParse()) {
				final String baseDir = parser.getFilePath()
						.substring(0, parser.getFilePath().lastIndexOf(File.separator) + 1);
				final List<AutomatonAST> automataDefinitionsFromOtherFiles = parseAutomataDefinitions(
						parser.getFilesToParse(), baseDir);
				// Check if automata from other files, were already defined in
				// current file.
				for (final AutomatonAST a : automataDefinitionsFromOtherFiles) {
					if (autDefs.hasAutomaton(a)) {
						mLogger.debug("Automaton \"" + a.getName() + "\" was already declared in file \""
								+ filename + "\".");
					} else {
						autDefs.addAutomaton(a);
					}
				}
			}
			ats.setAutomataDefinitions(autDefs);
			return (AutomataTestFileAST) result;
		} else {
			return null;
		}
	}

	/**
	 * Parses automata definitions from given files. This is usually required,
	 * if in a automata test file (.ats file) the
	 * parseAutomata(pathToAutomataDefinitions) is called.
	 * 
	 * @param filesToParse
	 *            the files from which to parse automata.
	 * @param baseDir
	 * @return list of automata, which are parsed from given files.
	 */
	private List<AutomatonAST> parseAutomataDefinitions(final List<String> filesToParse, final String baseDir) {
		final List<AutomatonAST> parsedAutomata = new ArrayList<AutomatonAST>();
		for (final String fileToParse : filesToParse) {
			Lexer lexer = null;
			final String fileSeparatorOfFileToParse = getFileSeparator(fileToParse);
			File file = null;
			if (fileSeparatorOfFileToParse != null) {
				file = openFile(adaptFileSeparators(fileToParse, fileSeparatorOfFileToParse), baseDir);
			} else {
				file = openFile(fileToParse, baseDir);
			}
			// if the file doesn't exist or couldn't open, then just skip
			// parsing of it.
			if (file == null) {
				continue;
			}
			try {
				lexer = new Lexer(new FileReader(file));
			} catch (final FileNotFoundException e) {
				mLogger.debug("File \"" + fileToParse + "\" doesn't exist or couldn't open!");
				continue;
			}
			final Parser p = new Parser(lexer,mLogger);
			p.setFileName(fileToParse);
			p.setFilePath(fileToParse);
			Object result = null;
			try {
				result = p.parse().value;
			} catch (final Exception e) {
				mLogger.debug("Parsing file \"" + fileToParse + "\" failed!");
				continue;
			}
			if ((result != null) && (result instanceof AutomataTestFileAST)) {
				final AutomataTestFileAST ats = (AutomataTestFileAST) result;
				if (!ats.getAutomataDefinitions().isEmpty()) {
					final List<AutomatonAST> newAutomataDefinitions = ats.getAutomataDefinitions()
							.getListOfAutomataDefinitions();
					for (final AutomatonAST a : newAutomataDefinitions) {
						if (parsedAutomata.contains(a)) {
							mLogger.debug("Automaton \"" + a.getName() + "\" from file \"" + fileToParse
									+ " already declared in other file.");
						} else {
							parsedAutomata.add(a);
						}
					}

				}
				mLogger.debug("\"" + fileToParse + "\" successfully parsed.");
			}
		}
		return parsedAutomata;
	}

	/**
	 * Opens a file, if the file exists and can be opened, and returns a file
	 * object, which is ready to read.
	 * 
	 * @param fileName
	 *            the file to open
	 * @param baseDir
	 *            the base directory of the file, which is currently parsed.
	 * @return null if the file doesn't exist or can't be opened, otherwise the
	 *         file object.
	 */
	private File openFile(final String fileName, String baseDir) {
		File file = new File(fileName);
		if (!file.exists() || !file.canRead()) {
			// In automata script files, the path for the
			// "parseAutomata"-operation
			// is allowed to contain ".." to reference the parent directory.
			if (fileName.startsWith(".." + File.separator)) {
				baseDir = baseDir.substring(0, baseDir.lastIndexOf(File.separator));
				baseDir = baseDir.substring(0, baseDir.lastIndexOf(File.separator) + 1);
				file = new File(baseDir + fileName.substring(3));
				if (!file.exists() || !file.canRead()) {
					mLogger.debug("File \"" + fileName + "\" doesn't exist or couldn't open!");
					return null;
				} else {
					return file;
				}
			} else {
				file = new File(baseDir + fileName);
				if (!file.exists() || !file.canRead()) {
					mLogger.debug("File \"" + fileName + "\" doesn't exist or couldn't open!");
					return null;
				} else {
					return file;
				}
			}
		}
		return file;
	}

	/**
	 * Checks if the given path contains file separators and returns the file
	 * separator in case it contains any.
	 * 
	 * @param path
	 *            the path, it may also be just a file name, like "example.ats".
	 * @return null if the path doesn't contain any file separator, otherwise it
	 *         returns found file separator.
	 */
	private String getFileSeparator(final String path) {
		if (path.contains("\\")) {
			return "\\";
		} else if (path.contains("/")) {
			return "/";
		} else {
			return null;
		}
	}

	/**
	 * Adapts file separators of the given path, if they are different to
	 * current OS file separator. It maintains platform-independence.
	 * 
	 * @param path
	 *            the path to a file
	 * @param containingFileSep
	 *            file separator contained in fileName.
	 * @return a path, where the file separators are conform to the OS file
	 *         separator.
	 */
	private String adaptFileSeparators(final String path, final String containingFileSep) {
		if (!containingFileSep.equals(System.getProperty("file.separator"))) {
			return path.replace(containingFileSep, System.getProperty("file.separator"));
		}
		return path;
	}

	/**
	 * Reports syntax error to Ultimate
	 * 
	 * @param longMessage
	 *            the string to be reported
	 * @param loc
	 *            the location of the string
	 */
	private void reportSyntaxError(final Severity sev, final String longMessage, final String shortMessage, final ILocation loc) {
		if (mServices == null) {
			throw new IllegalStateException();
		}
		final SyntaxErrorResult res = new SyntaxErrorResult(Activator.PLUGIN_ID, loc, longMessage);
		mServices.getResultService().reportResult(Activator.PLUGIN_ID, res);
		mLogger.info(shortMessage + " " + longMessage);
	}

	private static ILocation getPseudoLocation() {
		return new AutomataScriptLocation("", 0, 0, 0, 0);
	}

	/**
	 * @return the result
	 */
	public AutomataTestFileAST getResult() {
		return mResult;
	}
	
	

}
