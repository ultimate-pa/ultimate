package de.uni_freiburg.informatik.ultimate.ep.interfaces;

import java.io.File;

import de.uni_freiburg.informatik.ultimate.model.GraphType;
import de.uni_freiburg.informatik.ultimate.model.IElement;

/**
 * A generic parser interface which has to be implemented by parsers
 * 
 * @author Justus Bisser
 * @since 178
 * 
 * $LastChangedBy$
 * $LastChangedDate$
 * $LastChangedRevision$
 */
public interface ISource extends IToolchainPlugin {
	
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
	IElement parseAST(File[] files) throws Exception;

	/**
	 * Parse one single file
	 * @param file one single file that should be parsed
	 * can probably be a directory which can be parsed recursivly
	 * @return the root node of the parsed AST
	 */
	IElement parseAST(File file) throws Exception;
	
    
    /**
     * Use this to get a list of file types supported by this parser
     * @return Filename extensions supported by this parser.
     */
    String[] getFileTypes();
    
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
