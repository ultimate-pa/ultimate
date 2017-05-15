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
package de.uni_freiburg.informatik.ultimate.core.model;

import java.io.File;

import de.uni_freiburg.informatik.ultimate.core.model.models.IElement;
import de.uni_freiburg.informatik.ultimate.core.model.models.ModelType;

/**
 * A generic parser interface which has to be implemented by parsers
 *
 * @author Justus Bisser
 * @author Daniel Dietsch (dietsch@informatik.uni-freiburg.de)
 *
 */
public interface ISource extends IToolchainPlugin {

	/**
	 * Determine if some of the specified files can be parsed by this {@link ISource} plugin.F
	 *
	 * @param files
	 *            The candidate files.
	 *
	 * @return An array containing the files that can be parsed in the order they were presented in the input array or
	 *         an empty array if none of the files could be parsed.
	 */
	File[] parseable(final File[] files);

	/**
	 * Process this set of files and produce a model.
	 *
	 * @param files
	 *            the files that should be parsed (eg sourcefiles , projectfiles, folders).
	 *
	 * @return An {@link IElement} that represents the model created from the input files.
	 */
	IElement parseAST(final File[] files) throws Exception;

	/**
	 * @return The file extensions supported by this {@link ISource} plugin.
	 */
	String[] getFileTypes();

	/**
	 * This method is called by the core before a parser is executed. It should return structural informations about the
	 * model created by this {@link ISource} plugin.
	 *
	 * @return A {@link ModelType} object which describes the underlying graph structure of a model
	 */
	ModelType getOutputDefinition();
}
