/*
 * Copyright (C) 2013 University of Freiburg
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
package de.uni_freiburg.informatik.ultimate.smtinterpol.smtlib2;

/**
 * An asynchronous user cancellation request proxy.  SMTInterpol regularly polls
 * an object that implements this interface for user requests to terminate the
 * current search.  If cancellation is requested, SMTInterpol will set the 
 * reason to return unknown to 
 * {@link de.uni_freiburg.informatik.ultimate.logic.ReasonUnknown#CANCELLED}.
 * Once termination is requested, the solver keeps this state until the next
 * {@link de.uni_freiburg.informatik.ultimate.logic.Script#pop(int) pop}
 * command.
 * @author Juergen Christ
 */
public interface TerminationRequest {

	/**
	 * Check for termination.  If this returns <code>true</code> SMTInterpol
	 * will stop the current check and set the reason to return unknown to
	 * {@link de.uni_freiburg.informatik.ultimate.logic.ReasonUnknown#CANCELLED}.
	 * @return Should the current check be aborted.
	 */
	boolean isTerminationRequested();

}
