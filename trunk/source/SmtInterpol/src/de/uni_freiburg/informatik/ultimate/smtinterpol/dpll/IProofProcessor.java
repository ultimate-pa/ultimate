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
package de.uni_freiburg.informatik.ultimate.smtinterpol.dpll;

import java.io.PrintWriter;

import de.uni_freiburg.informatik.ultimate.smtinterpol.convert.Clausifier;

/**
 * Interface for all proof tree processors.  This interface only specifies one
 * method that is called when <code>(get-proof)</code> is used in the SMTLIB
 * input.  Register instances of this class with 
 * <code>(set-option :proof-processor "fully qualified class name")</code>.  As
 * an additional way, you can set the system property
 * <code>de.uni_freiburg.informatik.ultimate.smt.proof.processor</code> to the fully qualified class
 * name.  This will be used if there is no other proof processor available. 
 * @author Juergen Christ
 */
public interface IProofProcessor {
	/**
	 * Root method to process a proof tree.  Note that execution of the SMTLIB
	 * script is suspended only for the duration of this method.  If you want to
	 * block for a graphical output you should not return before the user closes
	 * the GUI.  Otherwise, the solver will close the GUI when it processes
	 * <code>(exit)</code>.  The parameters passed in this function are mostly
	 * for convenience.
	 * @param bottom		The root of the unsatisfiability tree (empty clause)
	 * @param clausifier	The formula converter used during this run.
	 * @param engine		The DPLL engine used during this run.
	 * @param out			The default output stream.
	 * @param err			The default error stream.
	 */
	public void process(Clause bottom, Clausifier clausifier,
			DPLLEngine engine, PrintWriter out, PrintWriter err);
}
