/*
 * Copyright (C) 2016 University of Freiburg
 *
 * This file is part of the Ultimate Delta Debugger plug-in.
 *
 * The Ultimate Delta Debugger plug-in is free software: you can redistribute it and/or modify
 * it under the terms of the GNU Lesser General Public License as published
 * by the Free Software Foundation, either version 3 of the License, or
 * (at your option) any later version.
 *
 * The Ultimate Delta Debugger plug-in is distributed in the hope that it will be useful,
 * but WITHOUT ANY WARRANTY; without even the implied warranty of
 * MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
 * GNU Lesser General Public License for more details.
 *
 * You should have received a copy of the GNU Lesser General Public License
 * along with the Ultimate Delta Debugger plug-in. If not, see <http://www.gnu.org/licenses/>.
 *
 * Additional permission under GNU GPL version 3 section 7:
 * If you modify the Ultimate Delta Debugger plug-in, or any covered work, by linking
 * or combining it with Eclipse RCP (or a modified version of Eclipse RCP),
 * containing parts covered by the terms of the Eclipse Public License, the
 * licensors of the Ultimate Delta Debugger plug-in grant you additional permission
 * to convey the resulting work.
 */
package de.uni_freiburg.informatik.ultimate.deltadebugger.core;

import org.eclipse.cdt.core.dom.ast.IASTTranslationUnit;

import de.uni_freiburg.informatik.ultimate.core.model.services.ILogger;
import de.uni_freiburg.informatik.ultimate.deltadebugger.core.parser.IParser;
import de.uni_freiburg.informatik.ultimate.deltadebugger.core.parser.pst.interfaces.IPSTTranslationUnit;
import de.uni_freiburg.informatik.ultimate.deltadebugger.core.text.ISourceDocument;

/**
 * A pass context provides the (immutable) input to a {@link IVariantGenerator}.
 * <p>
 * Important: The observable state of the context and the returned objects must not be changed, because they may be
 * shared with other passes.
 * <p>
 * A pass context instance holds a lazily computed AST and PST to prevent redundant parsing of the same input for
 * subsequent passes if there are no successful modifications in between. Global options that affect the algorithm of a
 * pass should eventually also go in here, e.g. predefined macros.
 */
public interface IPassContext {

	/**
	 * @return The input source code document.
	 */
	ISourceDocument getInput();

	/**
	 * @return The parser to be used for manual parsing.
	 */
	IParser getParser();

	/**
	 * Returns a lazily computed and internally cached AST instance for the input source code. This AST instance is
	 * shared with subsequent passes if no change is possible.
	 *
	 * @return the AST created with default options from the input source
	 */
	IASTTranslationUnit getSharedAst();

	/**
	 * Returns a lazily computed and internally cached APT instance for the input source code and the shared AST. This
	 * PST instance is shared with subsequent passes if no change is possible.
	 * <p>
	 * Note that the returned instance must not be modified to not affect other passes.
	 *
	 * @return the PST created with default options from the shared AST
	 */
	IPSTTranslationUnit getSharedPst();

	/**
	 * @return The logger instance to use for debug output.
	 */
	ILogger getLogger();
}
