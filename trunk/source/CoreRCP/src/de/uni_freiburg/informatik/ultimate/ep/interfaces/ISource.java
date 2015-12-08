/*
 * Copyright (C) 2007-2015 Daniel Dietsch (dietsch@informatik.uni-freiburg.de)
 * Copyright (C) 2015 Justus Bisser
 * Copyright (C) 2010-2015 Jürgen Christ (christj@informatik.uni-freiburg.de)
 * Copyright (C) 2015 University of Freiburg
 * 
 * This file is part of the ULTIMATE Core.
 * 
 * The ULTIMATE Core is free software: you can redistribute it and/or modify
 * it under the terms of the GNU Lesser General Public License as published
 * by the Free Software Foundation, either version 3 of the License, or
 * (at your option) any later version.
 * 
 * The ULTIMATE Core is distributed in the hope that it will be useful,
 * but WITHOUT ANY WARRANTY; without even the implied warranty of
 * MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
 * GNU Lesser General Public License for more details.
 * 
 * You should have received a copy of the GNU Lesser General Public License
 * along with the ULTIMATE Core. If not, see <http://www.gnu.org/licenses/>.
 * 
 * Additional permission under GNU GPL version 3 section 7:
 * If you modify the ULTIMATE Core, or any covered work, by linking
 * or combining it with Eclipse RCP (or a modified version of Eclipse RCP), 
 * containing parts covered by the terms of the Eclipse Public License, the 
 * licensors of the ULTIMATE Core grant you additional permission 
 * to convey the resulting work.
 */
package de.uni_freiburg.informatik.ultimate.ep.interfaces;

import java.io.File;

import de.uni_freiburg.informatik.ultimate.model.GraphType;
import de.uni_freiburg.informatik.ultimate.model.IElement;

/**
 * A generic parser interface which has to be implemented by parsers
 * 
 * @author Justus Bisser
 * 
 */
public interface ISource extends IToolchainPlugin {

	/**
	 * check if an array of files is parseable
	 * 
	 * @param files
	 *            to be checked
	 * 
	 * @return true if ALL of them are parseable would return an AST
	 */
	boolean parseable(File[] files);

	/**
	 * check if a file is parseable
	 * 
	 * @param file
	 *            to be checked
	 * 
	 * @return true if that file is parseable
	 */
	boolean parseable(File file);

	/**
	 * when ever the core wants something parsed he will call a parser with this
	 * method.
	 * 
	 * @param files
	 *            - the files that should be parsed (eg sourcefiles ,
	 *            projectfiles, folders)
	 * 
	 * @return the Root node of the parsed AST
	 */
	IElement parseAST(File[] files) throws Exception;

	/**
	 * Parse one single file
	 * 
	 * @param file
	 *            one single file that should be parsed can probably be a
	 *            directory which can be parsed recursivly
	 * @return the root node of the parsed AST
	 */
	IElement parseAST(File file) throws Exception;

	/**
	 * Use this to get a list of file types supported by this parser
	 * 
	 * @return Filename extensions supported by this parser.
	 */
	String[] getFileTypes();

	/**
	 * This method is called by the core before a parser is executed. It should
	 * return structural informations about the model created by the parser.
	 * 
	 * @return A GraphType object which describes the underlying graph structure
	 *         of a model
	 */
	GraphType getOutputDefinition();

	/**
	 * This method is used by the core to set the prelude file for the parser.
	 * 
	 * @param prelude
	 */
	void setPreludeFile(File prelude);
}
