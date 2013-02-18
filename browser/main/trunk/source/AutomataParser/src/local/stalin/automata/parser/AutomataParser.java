package local.stalin.automata.parser;

import java.io.File;
import org.apache.log4j.Level;

import local.stalin.core.api.StalinServices;
import local.stalin.ep.interfaces.ISource;
import local.stalin.model.GraphType;
import local.stalin.model.INode;
import local.stalin.model.TokenMap;
import org.apache.log4j.Logger;
import java.util.*;

 /**
  * TODO kurze Beschreibung der Klasse auf englisch. 
  * Stalin plugin for parsing a test case for the automaton-plugin 
  * 
  * @author heizmann@informatik.uni-freiburg.de
  *         Jan Mortensen
  *         Daniel Christiany
  *
  */




public class AutomataParser implements ISource {

	//This file parses a sablecc ast and transforms it to a stalin ast
	private ASTBuilder astBuilder;
	
	private static Logger s_Logger = 
			StalinServices.getInstance().getLogger(Activator.PLUGIN_ID);
    protected List<String> m_FileNames;
    protected String[] m_FileTypes;
    
    
	public AutomataParser(){
		m_FileTypes = new String[] { "fat" };
		astBuilder = new ASTBuilder(this);
	}

	
	public String[] getFileTypes() {
		return m_FileTypes;
	}

	
	@Override
	public GraphType getOutputDefinition() {
		try {
			return new GraphType(getPluginID(), GraphType.Type.AST,this.m_FileNames);
		} catch (Exception ex) {
			s_Logger.log(Level.FATAL, ex.getMessage());
			return null;
		}
	}

	
	@Override
	public TokenMap getTokenMap() {
		s_Logger.warn("getTokenMap() is called by STALIN. I do not know why and what it does, " +
				"but return a new TokenMap() and everything works fine.");
		return new TokenMap();
	}

	
	@Override
	public String[] getTokens() {
		throw new UnsupportedOperationException("This operation is not supported by Automata Parser");
	}

	
	@Override
	public INode parseAST(File[] files) throws Exception {
		s_Logger.warn("Automata Parser can not parse more than one file. Parsing only " + files[0].getName() +
				"and ignoring the other input files");
		return parseAST(files[0]);
	}

	
	@Override
	public INode parseAST(File file) throws Exception {
		m_FileNames.add(file.getName());
		astBuilder.parse(file);
		return astBuilder.getAST();
	}

	
    /**
     * Gets a list of files and checks whether all of them are
     * parseable by this parser. In good DOS tradition we use
     * file extensions to accomplish this task ;-)
     * 
     * @param files a list of files to check
     * @return true if parseable
     * @see local.stalin.ep.interfaces.IParser#parseable(java.io.File[])
     */
    public boolean parseable(File[] files) {
        for (File f : files) {
            if (!parseable(f)) { return false; }
        }
        return true;
    }

    
    /**
     * Gets a file and checks whether it is
     * parseable by this parser. In good DOS tradition we use
     * file extensions to accomplish this task ;-)
     * 
     * @param file the file to be checked
     * @return true if parseable
     * @see local.stalin.ep.interfaces.IParser#parseable(java.io.File)
     */
    public boolean parseable(File file) {
    	for(String s : getFileTypes())
    	{
    		if(file.getName().endsWith(s))
    			return true;
    	}
        return false;
    }
	
    
	@Override
	public String getName() {
		return Activator.PLUGIN_ID;
	}

	
	@Override
	public String getPluginID() {
		return Activator.PLUGIN_ID;
	}

	
	/**
     * This initializes the plugin. Parsers usually do not get
     * parameters so we will just return 0 for anything.
     * 
     * @param param is ignored
     * @see local.stalin.ep.interfaces.IStalinPlugin#init()
     */
    public int init(Object param) {
    	m_FileNames = new ArrayList<String>();
        return 0;
    }


	@Override
	public void setPreludeFile(File prelude) {
		//AutomataParser does not use prelude files
	}

}
