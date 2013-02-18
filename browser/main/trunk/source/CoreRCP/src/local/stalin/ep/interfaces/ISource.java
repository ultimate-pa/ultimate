package local.stalin.ep.interfaces;

import java.io.File;

import local.stalin.model.GraphType;
import local.stalin.model.INode;
import local.stalin.model.TokenMap;

/**
 * A generic parser interface which has to be implemented by parsers
 * 
 * @author Justus Bisser
 * @since 178
 * 
 * $LastChangedBy: christj $
 * $LastChangedDate: 2010-04-12 10:18:09 +0200 (Mo, 12. Apr 2010) $
 * $LastChangedRevision: 2254 $
 */
public interface ISource extends IStalinPlugin {


	
	/**
	 * check if an array of files is parseable
	 * @param files to be checked
	 * 
	 * @return true if ALL of them are parseable
	 * would return an AST
	 */
	boolean parseable(File[] files);

	/**
	 * check if a file is parseable
	 * 
	 * @param file to be checked
	 * 
	 * @return true if that file is parseable
	 */
	boolean parseable(File file);

	/**
	 * when ever the core wants something parsed he will call a parser 
	 * with this method.
	 * 
	 * @param files - the files that should be parsed 
	 * (eg sourcefiles , projectfiles, folders)
	 * 
	 * @return the Root node of the parsed AST
	 */
	INode parseAST(File[] files) throws Exception;

	/**
	 * Parse one single file
	 * @param file one single file that should be parsed
	 * can probably be a directory which can be parsed recursivly
	 * @return the root node of the parsed AST
	 */
	INode parseAST(File file) throws Exception;
	
	/**
	 * Ask the parser for it's supported tokens.
	 * @return a Sting array with the tokens
	 */
	String[] getTokens();
    
    /**
     * Use this to get a list of file types supported by this parser
     * @return Filename extensions supported by this parser.
     */
    String[] getFileTypes();
    
    /**
     * retrieves a map with all token mappings
     * @return the map
     */
    public TokenMap getTokenMap();
    
	/**
	 * This method is called by the core before a parser is executed. 
	 * It should return structural informations about the model created by the parser. 
	 *  
	 * @return A GraphType object which describes the underlying graph structure of a model
	 */
	GraphType getOutputDefinition();
	
	/**
	 * This method is used by the core to set the prelude file for the parser.
	 * 
	 * @param prelude
	 */
	void setPreludeFile(File prelude);
}
