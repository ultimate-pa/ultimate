package de.uni_freiburg.informatik.ultimate.plugins.source.automatascriptparser;

import java.io.File;
import java.io.FileNotFoundException;
import java.io.FileReader;
import java.util.ArrayList;
import java.util.List;

import org.apache.log4j.Logger;

import de.uni_freiburg.informatik.ultimate.core.api.UltimateServices;
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
			reportToUltimate(Severity.ERROR, parser.getLongErrorMessage(),
					         parser.getShortErrorMessage(), 
					         parser.getErrorLocation());
			return null;
		}

		String successMessage = "'" + file.getName() + "' successfully parsed"; 
		s_Logger.info(successMessage);
		if (result instanceof AutomataTestFile) {
			AutomataTestFile ats = (AutomataTestFile)result;
			AutomataDefinitions autDefs = ats.getAutomataDefinitions();
			
			if (parser.containsOtherAutomataFilesToParse()) {
				String baseDir = parser.getFilePath().substring(0, parser.getFilePath().lastIndexOf(File.separator) + 1);
				List<Automaton> automataDefinitionsFromOtherFiles = parseAutomataDefinitions(parser.getFilesToParse(), baseDir);
				for (Automaton a : automataDefinitionsFromOtherFiles) {
					if (autDefs.hasAutomaton(a)) {
						s_Logger.error("Automaton \"" + a.getName() + "\" was already declared in file \"" + file.getName() + "\".");
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
	 * 
	 * @param filesToParse
	 * @param baseDir
	 * @return
	 */
	private List<Automaton> parseAutomataDefinitions(List<String> filesToParse, String baseDir) {
		List<Automaton> parsedAutomata = new ArrayList<Automaton>();
		for (String fileToParse : filesToParse) {
			Lexer l = null;
			String fileSeparatorOfFileToParse = getFileSeparator(fileToParse);
			File file = null;
			if (fileSeparatorOfFileToParse != null) {
				file = openFile(adaptFileSeparators(fileToParse, fileSeparatorOfFileToParse), baseDir);
			} else {
				file = openFile(fileToParse, baseDir);
			}
			if (file == null) {
				continue;
			}
			try {
				l = new Lexer(new FileReader(file));
			} catch (FileNotFoundException e) {
				s_Logger.error("File \"" + fileToParse + "\" doesn't exist or couldn't open!");
				e.printStackTrace();
				continue;
			}
			Parser p = new Parser(l);
			p.setFileName(fileToParse);
			p.setFilePath(fileToParse);
			Object result = null;
			try {
				result = p.parse().value;
			} catch (Exception e) {
				s_Logger.error("Parsing file \"" + fileToParse + "\" failed!");
				e.printStackTrace();
				continue;
			}
			if ((result != null) && (result instanceof AutomataTestFile)) {
				AutomataTestFile ats = (AutomataTestFile) result;
				if (!ats.getAutomataDefinitions().isEmpty()) {
					List<Automaton> newAutomataDefinitions = ats.getAutomataDefinitions().getListOfAutomataDefinitions();
					for (Automaton a : newAutomataDefinitions) {
						if (parsedAutomata.contains(a)) {
							s_Logger.error("Automaton \"" + a.getName() + "\" from file \"" + fileToParse + " already declared in other file.");
						} else {
							parsedAutomata.add(a);
						}
					}
					
				}
				s_Logger.info("\"" + fileToParse + "\" successfully parsed.");
			}
		}
		return parsedAutomata;
	}
	
	private File openFile(String fileName, String baseDir) {
		File f = new File(fileName);
		if (!f.exists() || !f.canRead()) {
			if (fileName.startsWith(".." + File.separator)) {
				baseDir = baseDir.substring(0, baseDir.lastIndexOf(File.separator));
				baseDir = baseDir.substring(0, baseDir.lastIndexOf(File.separator) + 1);
				f = new File(baseDir + fileName.substring(3));
				if (!f.exists() || !f.canRead()) {
					s_Logger.error("File \"" + fileName + "\" doesn't exist or couldn't open!");
					return null;
				} else {
					return f;
				}
			} else {
				f = new File(baseDir + fileName);
				if (!f.exists() || !f.canRead()) {
					s_Logger.error("File \"" + fileName + "\" doesn't exist or couldn't open!");
					return null;
				} else {
					return f;
				}
			}
		}
		return f;
	}
		
	/**
	 * Checks if the given file name contains file separators and returns
	 * the file separator in case it contains any.
	 * @param fileName
	 * @return null if the fileName doesn't contain any file separator, otherwise it returns found file separator
	 */
	private String getFileSeparator(String fileName) {
		if (fileName.contains("\\")) {
			return "\\";
		} else if (fileName.contains("/")) {
			return "/";
		} else {
			return null;
		}
	}
	
	
	private String adaptFileSeparators(String fileName, String containingFileSep) {
		if (!containingFileSep.equals(File.separator)) {
			return fileName.replace(containingFileSep, File.separator);
		}
		return fileName;
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

}
