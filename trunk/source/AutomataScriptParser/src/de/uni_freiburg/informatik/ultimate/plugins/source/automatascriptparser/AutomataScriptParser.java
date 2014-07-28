package de.uni_freiburg.informatik.ultimate.plugins.source.automatascriptparser;

import java.io.File;
import java.io.FileNotFoundException;
import java.io.FileReader;
import java.util.ArrayList;
import java.util.List;

import javax.print.attribute.standard.Severity;

import org.apache.log4j.Logger;

import de.uni_freiburg.informatik.ultimate.core.preferences.UltimatePreferenceInitializer;
import de.uni_freiburg.informatik.ultimate.core.services.IToolchainStorage;
import de.uni_freiburg.informatik.ultimate.core.services.IUltimateServiceProvider;
import de.uni_freiburg.informatik.ultimate.ep.interfaces.ISource;
import de.uni_freiburg.informatik.ultimate.model.GraphType;
import de.uni_freiburg.informatik.ultimate.model.IElement;
import de.uni_freiburg.informatik.ultimate.model.location.ILocation;
import de.uni_freiburg.informatik.ultimate.plugins.source.automatascriptparser.AST.AutomataDefinitionsAST;
import de.uni_freiburg.informatik.ultimate.plugins.source.automatascriptparser.AST.AutomataTestFileAST;
import de.uni_freiburg.informatik.ultimate.plugins.source.automatascriptparser.AST.AutomatonAST;
import de.uni_freiburg.informatik.ultimate.result.SyntaxErrorResult;

public class AutomataScriptParser implements ISource {

	protected String[] mFileTypes = new String[] { "ats" };

	protected List<String> mFileNames = new ArrayList<String>();

	private Logger mLogger;

	private IUltimateServiceProvider mServices;

	private IElement parseFile(File file) throws Exception {
		Lexer lexer = new Lexer(new FileReader(file));
		Parser parser = new Parser(lexer, mLogger);
		parser.setFileName(file.getName());
		parser.setFilePath(file.getAbsolutePath());

		Object result = null;
		try {
			result = parser.parse().value;
		} catch (Exception e) {
			ILocation location = parser.getErrorLocation();
			if (location == null) {
				mLogger.debug("Error without location");
				location = getPseudoLocation();
			}
			String shortErrorMessage = parser.getShortErrorMessage();
			if (shortErrorMessage == null) {
				shortErrorMessage = e.getMessage();
			}
			String longErrorMessage = parser.getShortErrorMessage();
			if (longErrorMessage == null) {
				longErrorMessage = e.getMessage();
			}
			reportSyntaxError(Severity.ERROR, longErrorMessage, shortErrorMessage, location);
			mLogger.info("Parsing aborted.");
			return null;
		}

		mLogger.debug("'" + file.getName() + "' successfully parsed");
		if (result instanceof AutomataTestFileAST) {
			AutomataTestFileAST ats = (AutomataTestFileAST) result;
			AutomataDefinitionsAST autDefs = ats.getAutomataDefinitions();
			// parser contains files to parse, if the operation
			// parseAutomata(pathToFile) was called at least
			// once.
			if (parser.containsOtherAutomataFilesToParse()) {
				String baseDir = parser.getFilePath()
						.substring(0, parser.getFilePath().lastIndexOf(File.separator) + 1);
				List<AutomatonAST> automataDefinitionsFromOtherFiles = parseAutomataDefinitions(
						parser.getFilesToParse(), baseDir);
				// Check if automata from other files, were already defined in
				// current file.
				for (AutomatonAST a : automataDefinitionsFromOtherFiles) {
					if (autDefs.hasAutomaton(a)) {
						mLogger.debug("Automaton \"" + a.getName() + "\" was already declared in file \""
								+ file.getName() + "\".");
					} else {
						autDefs.addAutomaton(a);
					}
				}
			}
			ats.setAutomataDefinitions(autDefs);
			return (AtsASTNode) result;
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
	private List<AutomatonAST> parseAutomataDefinitions(List<String> filesToParse, String baseDir) {
		List<AutomatonAST> parsedAutomata = new ArrayList<AutomatonAST>();
		for (String fileToParse : filesToParse) {
			Lexer lexer = null;
			String fileSeparatorOfFileToParse = getFileSeparator(fileToParse);
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
			} catch (FileNotFoundException e) {
				mLogger.debug("File \"" + fileToParse + "\" doesn't exist or couldn't open!");
				continue;
			}
			Parser p = new Parser(lexer,mLogger);
			p.setFileName(fileToParse);
			p.setFilePath(fileToParse);
			Object result = null;
			try {
				result = p.parse().value;
			} catch (Exception e) {
				mLogger.debug("Parsing file \"" + fileToParse + "\" failed!");
				continue;
			}
			if ((result != null) && (result instanceof AutomataTestFileAST)) {
				AutomataTestFileAST ats = (AutomataTestFileAST) result;
				if (!ats.getAutomataDefinitions().isEmpty()) {
					List<AutomatonAST> newAutomataDefinitions = ats.getAutomataDefinitions()
							.getListOfAutomataDefinitions();
					for (AutomatonAST a : newAutomataDefinitions) {
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
	private File openFile(String fileName, String baseDir) {
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
	private String getFileSeparator(String path) {
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
	private String adaptFileSeparators(String path, String containingFileSep) {
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
	private void reportSyntaxError(Severity sev, String longMessage, String shortMessage, ILocation loc) {
		if (mServices == null) {
			throw new IllegalStateException();
		}
		SyntaxErrorResult res = new SyntaxErrorResult(Activator.s_PLUGIN_ID, loc, longMessage);
		mServices.getResultService().reportResult(Activator.s_PLUGIN_ID, res);
		mLogger.info(shortMessage + " " + longMessage);
	}

	@Override
	public String[] getFileTypes() {
		return mFileTypes;
	}

	@Override
	public GraphType getOutputDefinition() {
		try {
			return new GraphType(getPluginID(), GraphType.Type.AST, this.mFileNames);
		} catch (Exception ex) {
			mLogger.fatal(ex.getMessage());
			return null;
		}
	}

	@Override
	public IElement parseAST(File[] files) throws Exception {
		mLogger.warn("AutomataScriptParser can not parse more than one file. Parsing only " + files[0].getName()
				+ "and ignoring the other input files");
		return parseAST(files[0]);
	}

	@Override
	public IElement parseAST(File file) throws Exception {
		mFileNames.add(file.getName());
		mLogger.info("Parsing '" + file.getAbsolutePath() + "'");
		return parseFile(file);
	}

	@Override
	public boolean parseable(File[] files) {
		for (File f : files) {
			if (!parseable(f)) {
				return false;
			}
		}
		return true;
	}

	@Override
	public boolean parseable(File file) {
		for (String s : getFileTypes()) {
			if (file.getName().endsWith(s))
				return true;
		}
		return false;
	}

	@Override
	public void setPreludeFile(File prelude) {
		// TODO Auto-generated method stub

	}

	@Override
	public String getPluginName() {
		return Activator.s_PLUGIN_NAME;
	}

	@Override
	public String getPluginID() {
		return Activator.s_PLUGIN_ID;
	}

	@Override
	public int init() {
		return 0;
	}

	private static ILocation getPseudoLocation() {
		return new AutomataScriptLocation("", 0, 0, 0, 0);
	}

	@Override
	public UltimatePreferenceInitializer getPreferences() {
		// TODO Auto-generated method stub
		return null;
	}

	@Override
	public void setToolchainStorage(IToolchainStorage storage) {

	}

	@Override
	public void setServices(IUltimateServiceProvider services) {
		mServices = services;
		mLogger = mServices.getLoggingService().getLogger(Activator.s_PLUGIN_ID);
	}

}
