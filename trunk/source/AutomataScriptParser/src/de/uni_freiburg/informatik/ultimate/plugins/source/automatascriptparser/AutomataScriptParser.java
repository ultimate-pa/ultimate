package de.uni_freiburg.informatik.ultimate.plugins.source.automatascriptparser;

import java.io.File;
import java.io.FileNotFoundException;
import java.io.FileReader;
import java.util.ArrayList;
import java.util.List;

import org.apache.log4j.Logger;

import de.uni_freiburg.informatik.ultimate.core.api.UltimateServices;
import de.uni_freiburg.informatik.ultimate.core.preferences.UltimatePreferenceInitializer;
import de.uni_freiburg.informatik.ultimate.ep.interfaces.ISource;
import de.uni_freiburg.informatik.ultimate.model.GraphType;
import de.uni_freiburg.informatik.ultimate.model.IElement;
import de.uni_freiburg.informatik.ultimate.model.ILocation;
import de.uni_freiburg.informatik.ultimate.model.TokenMap;
import de.uni_freiburg.informatik.ultimate.plugins.source.automatascriptparser.AST.AutomataDefinitions;
import de.uni_freiburg.informatik.ultimate.plugins.source.automatascriptparser.AST.AutomataTestFile;
import de.uni_freiburg.informatik.ultimate.plugins.source.automatascriptparser.AST.Automaton;
import de.uni_freiburg.informatik.ultimate.result.GenericResult;
import de.uni_freiburg.informatik.ultimate.result.GenericResult.Severity;


public class AutomataScriptParser implements ISource {
	
	protected String[] m_FileTypes = new String[] {"ats"};

    protected List<String> m_FileNames = new ArrayList<String>();

	public static Logger s_Logger = UltimateServices.getInstance().getLogger(Activator.s_PLUGIN_ID);
	
	
	private IElement parseFile(File file) throws Exception {
		Lexer lexer = new Lexer(new FileReader(file));
		Parser parser = new Parser(lexer);
		parser.setFileName(file.getName());
		parser.setFilePath(file.getAbsolutePath());
		
		Object result = null;
		try {
			result = parser.parse().value;
		} catch (Exception e) {
			ILocation location = parser.getErrorLocation();
			if (location == null) {
				s_Logger.debug("Error without location");
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
			reportToUltimate(Severity.ERROR, longErrorMessage,
					shortErrorMessage, 
					location);
			s_Logger.info("Parsing aborted.");
			return null;
		}

		
		s_Logger.debug("'" + file.getName() + "' successfully parsed");
		if (result instanceof AutomataTestFile) {
			AutomataTestFile ats = (AutomataTestFile)result;
			AutomataDefinitions autDefs = ats.getAutomataDefinitions();
			// parser contains files to parse, if the operation parseAutomata(pathToFile) was called at least
			// once.
			if (parser.containsOtherAutomataFilesToParse()) {
				String baseDir = parser.getFilePath().substring(0, parser.getFilePath().lastIndexOf(File.separator) + 1);
				List<Automaton> automataDefinitionsFromOtherFiles = parseAutomataDefinitions(parser.getFilesToParse(), baseDir);
				// Check if automata from other files, were already defined in current file.
				for (Automaton a : automataDefinitionsFromOtherFiles) {
					if (autDefs.hasAutomaton(a)) {
						s_Logger.debug("Automaton \"" + a.getName() + "\" was already declared in file \"" + file.getName() + "\".");
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
	 * Parses automata definitions from given files. This is usually required, if
	 * in a automata test file (.ats file) the parseAutomata(pathToAutomataDefinitions) is called.
	 * @param filesToParse the files from which to parse automata.
	 * @param baseDir 
	 * @return list of automata, which are parsed from given files.
	 */
	private List<Automaton> parseAutomataDefinitions(List<String> filesToParse, String baseDir) {
		List<Automaton> parsedAutomata = new ArrayList<Automaton>();
		for (String fileToParse : filesToParse) {
			Lexer lexer = null;
			String fileSeparatorOfFileToParse = getFileSeparator(fileToParse);
			File file = null;
			if (fileSeparatorOfFileToParse != null) {
				file = openFile(adaptFileSeparators(fileToParse, fileSeparatorOfFileToParse), baseDir);
			} else {
				file = openFile(fileToParse, baseDir);
			}
			// if the file doesn't exist or couldn't open, then just skip parsing of it.
			if (file == null) {
				continue;
			}
			try {
				lexer = new Lexer(new FileReader(file));
			} catch (FileNotFoundException e) {
				s_Logger.debug("File \"" + fileToParse + "\" doesn't exist or couldn't open!");
				continue;
			}
			Parser p = new Parser(lexer);
			p.setFileName(fileToParse);
			p.setFilePath(fileToParse);
			Object result = null;
			try {
				result = p.parse().value;
			} catch (Exception e) {
				s_Logger.debug("Parsing file \"" + fileToParse + "\" failed!");
				continue;
			}
			if ((result != null) && (result instanceof AutomataTestFile)) {
				AutomataTestFile ats = (AutomataTestFile) result;
				if (!ats.getAutomataDefinitions().isEmpty()) {
					List<Automaton> newAutomataDefinitions = ats.getAutomataDefinitions().getListOfAutomataDefinitions();
					for (Automaton a : newAutomataDefinitions) {
						if (parsedAutomata.contains(a)) {
							s_Logger.debug("Automaton \"" + a.getName() + "\" from file \"" + fileToParse + " already declared in other file.");
						} else {
							parsedAutomata.add(a);
						}
					}
					
				}
				s_Logger.debug("\"" + fileToParse + "\" successfully parsed.");
			}
		}
		return parsedAutomata;
	}
	
	
	/**
	 * Opens a file, if the file exists and can be opened, and returns a file object,
	 * which is ready to read.
	 * @param fileName the file to open
	 * @param baseDir the base directory of the file, which is currently parsed.
	 * @return null if the file doesn't exist or can't be opened, otherwise the file object.
	 */
	private File openFile(String fileName, String baseDir) {
		File file = new File(fileName);
		if (!file.exists() || !file.canRead()) {
			// In automata script files, the path for the "parseAutomata"-operation
			// is allowed to contain ".." to reference the parent directory.
			if (fileName.startsWith(".." + File.separator)) {
				baseDir = baseDir.substring(0, baseDir.lastIndexOf(File.separator));
				baseDir = baseDir.substring(0, baseDir.lastIndexOf(File.separator) + 1);
				file = new File(baseDir + fileName.substring(3));
				if (!file.exists() || !file.canRead()) {
					s_Logger.debug("File \"" + fileName + "\" doesn't exist or couldn't open!");
					return null;
				} else {
					return file;
				}
			} else {
				file = new File(baseDir + fileName);
				if (!file.exists() || !file.canRead()) {
					s_Logger.debug("File \"" + fileName + "\" doesn't exist or couldn't open!");
					return null;
				} else {
					return file;
				}
			}
		}
		return file;
	}
		
	/**
	 * Checks if the given path contains file separators and returns
	 * the file separator in case it contains any.
	 * @param path the path, it may also be just a file name, like "example.ats".
	 * @return null if the path doesn't contain any file separator, otherwise it returns found file separator.
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
	 * Adapts file separators of the given path, if they are different to current
	 * OS file separator. It maintains platform-independence. 
	 * @param path the path to a file
	 * @param containingFileSep file separator contained in fileName.
	 * @return a path, where the file separators are conform to the OS file separator. 
	 */
	private String adaptFileSeparators(String path, String containingFileSep) {
		if (!containingFileSep.equals(System.getProperty("file.separator"))) {
			return path.replace(containingFileSep, System.getProperty("file.separator"));
		}
		return path;
	}
	
	


	/**
	 * Reports the given string with the given severity to Ultimate as a GenericResult
	 * @param sev the severity
	 * @param longMessage the string to be reported
	 * @param loc the location of the string
	 */
	private static void reportToUltimate(Severity sev, String longMessage, String shortMessage, ILocation loc) {
		    GenericResult<Integer> res = new GenericResult<Integer>((loc != null? loc.getStartLine() : -1),
		    		                     Activator.s_PLUGIN_ID,
		    		                     null,
		    		                     loc,
		    		                     shortMessage, longMessage, 
		    		                     sev);
			UltimateServices.getInstance().reportResult(Activator.s_PLUGIN_ID, res);
			s_Logger.info(shortMessage + " " + longMessage);
	}
	
	
	
	/* (non-Javadoc)
	 * @see de.uni_freiburg.informatik.ultimate.ep.interfaces.ISource#getFileTypes()
	 */
	@Override
	public String[] getFileTypes() {
        return m_FileTypes;
    }

	/* (non-Javadoc)
	 * @see de.uni_freiburg.informatik.ultimate.ep.interfaces.ISource#getOutputDefinition()
	 */
	@Override
	public GraphType getOutputDefinition() {
		try {
			return new GraphType(getPluginID(), GraphType.Type.AST,this.m_FileNames);
		} catch (Exception ex) {
			s_Logger.fatal(ex.getMessage());
			return null;
		}
	}

	/* (non-Javadoc)
	 * @see de.uni_freiburg.informatik.ultimate.ep.interfaces.ISource#getTokenMap()
	 */
	@Override
	public TokenMap getTokenMap() {
		// I don't use TokenMap
		return null;
	}

	/* (non-Javadoc)
	 * @see de.uni_freiburg.informatik.ultimate.ep.interfaces.ISource#getTokens()
	 */
	@Override
	public String[] getTokens() {
		// TODO Auto-generated method stub
		return null;
	}

	/* (non-Javadoc)
	 * @see de.uni_freiburg.informatik.ultimate.ep.interfaces.ISource#parseAST(java.io.File[])
	 */
	@Override
	public IElement parseAST(File[] files) throws Exception {
		s_Logger.warn("AutomataScriptParser can not parse more than one file. Parsing only " + files[0].getName() +
				"and ignoring the other input files");
		return parseAST(files[0]);
	}

	/* (non-Javadoc)
	 * @see de.uni_freiburg.informatik.ultimate.ep.interfaces.ISource#parseAST(java.io.File)
	 */
	@Override
	public IElement parseAST(File file) throws Exception {
		m_FileNames.add(file.getName());
		s_Logger.info("Parsing '" + file.getAbsolutePath() + "'");
		return parseFile(file);
	}

	/* (non-Javadoc)
	 * @see de.uni_freiburg.informatik.ultimate.ep.interfaces.ISource#parseable(java.io.File)
	 */
	@Override
    public boolean parseable(File[] files) {
        for (File f : files) {
            if (!parseable(f)) { return false; }
        }
        return true;
    }

	/* (non-Javadoc)
	 * @see de.uni_freiburg.informatik.ultimate.ep.interfaces.ISource#parseable(java.io.File)
	 */
	@Override
	public boolean parseable(File file) {
		for(String s : getFileTypes())
    	{
    		if(file.getName().endsWith(s))
    			return true;
    	}
        return false;
	}

	/* (non-Javadoc)
	 * @see de.uni_freiburg.informatik.ultimate.ep.interfaces.ISource#setPreludeFile(java.io.File)
	 */
	@Override
	public void setPreludeFile(File prelude) {
		// TODO Auto-generated method stub

	}

	/* (non-Javadoc)
	 * @see de.uni_freiburg.informatik.ultimate.ep.interfaces.IRCPPlugin#getName()
	 */
	@Override
	public String getName() {
		return Activator.s_PLUGIN_NAME;
	}

	/* (non-Javadoc)
	 * @see de.uni_freiburg.informatik.ultimate.ep.interfaces.IRCPPlugin#getPluginID()
	 */
	@Override
	public String getPluginID() {
		return Activator.s_PLUGIN_ID;
	}

	/* (non-Javadoc)
	 * @see de.uni_freiburg.informatik.ultimate.ep.interfaces.IRCPPlugin#init(java.lang.Object)
	 */
	@Override
	public int init(Object params) {
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

}
