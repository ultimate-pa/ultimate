/*
 * Copyright (C) 2009-2012 University of Freiburg
 *
 * This file is part of SMTInterpol.
 *
 * SMTInterpol is free software: you can redistribute it and/or modify
 * it under the terms of the GNU Lesser General Public License as published
 * by the Free Software Foundation, either version 3 of the License, or
 * (at your option) any later version.
 *
 * SMTInterpol is distributed in the hope that it will be useful,
 * but WITHOUT ANY WARRANTY; without even the implied warranty of
 * MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
 * GNU Lesser General Public License for more details.
 *
 * You should have received a copy of the GNU Lesser General Public License
 * along with SMTInterpol.  If not, see <http://www.gnu.org/licenses/>.
 */
package de.uni_freiburg.informatik.ultimate.smtinterpol;

import de.uni_freiburg.informatik.ultimate.logic.Script;

/**
 * Generic interface for the different parsers of SMTInterpol.  Each interface
 * (SMTLIB, SMTLIB 2, DIMACS,...) should provide an implementation of this
 * interface to be used by the generic main method.
 * @author Juergen Christ
 */
public interface IParser {
    /**
	 * Set the backend solver.  This must be called before setting any
	 * options or including a file.
	 */
	public void setSolver(Script solver);

	/**
	 * Set an option.  This should piped through to the underlying solver.
	 * An implementing class may use this to react to certain options,
	 * e.g., :print-success.
	 */
	public void setOption(String option, Object value);

	/**
	 * Parse a specific file. If the filename is <code>null</code>, the
	 * parser should parse standard input.
	 * @param filename  The name of the file to parse.
	 * @return Exit code.
	 */
	public int parseFile(String filename); 
}
