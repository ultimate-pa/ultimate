/*
 * Copyright (C) 2017 Matthias Heizmann (heizmann@informatik.uni-freiburg.de)
 * Copyright (C) 2017 University of Freiburg
 *
 * This file is part of the ULTIMATE ModelCheckerUtils Library.
 *
 * The ULTIMATE ModelCheckerUtils Library is free software: you can redistribute it and/or modify
 * it under the terms of the GNU Lesser General Public License as published
 * by the Free Software Foundation, either version 3 of the License, or
 * (at your option) any later version.
 *
 * The ULTIMATE ModelCheckerUtils Library is distributed in the hope that it will be useful,
 * but WITHOUT ANY WARRANTY; without even the implied warranty of
 * MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
 * GNU Lesser General Public License for more details.
 *
 * You should have received a copy of the GNU Lesser General Public License
 * along with the ULTIMATE ModelCheckerUtils Library. If not, see <http://www.gnu.org/licenses/>.
 *
 * Additional permission under GNU GPL version 3 section 7:
 * If you modify the ULTIMATE ModelCheckerUtils Library, or any covered work, by linking
 * or combining it with Eclipse RCP (or a modified version of Eclipse RCP),
 * containing parts covered by the terms of the Eclipse Public License, the
 * licensors of the ULTIMATE ModelCheckerUtils Library grant you additional permission
 * to convey the resulting work.
 */
package de.uni_freiburg.informatik.ultimate.modelcheckerutils.taskidentifier;

/**
 * Objects of this type (and its subclasses) are only used to generate strings.
 * In several parts of Ultimate we would like to have unique identifiers for
 * dumping things (e.g., SMT scripts, automata, pathprograms) to files.
 * Using local information for generating the strings was not sufficient.
 * E.g., a TrackCheck can be done 
 * <ul>
 * <li> while checking if a MapElimination was an overapproximation 
 * <li> while checking termination, 
 * <li> while checking for the existance of a danger invariant in a path program
 * <li> in iteration 42 of a CEGAR loop
 * <li> while verifying the 23rd specification of
 * <li> an input program whose filename is x.
 * </ul>
 * Each {@link TaskIdentifier} takes the {@link TaskIdentifier} of its parent
 * task (null if topmost) and can generate a stings that identifies the current
 * subtask (e.g., Iteration42). The generation of the subtask string is defined
 * by the subclasses of this class.
 * These {@link TaskIdentifier} form a singly linked list and strings are 
 * constructed each time anew, but performance is irrelevant here.
 * 
 * @author Matthias Heizmann (heizmann@informatik.uni-freiburg.de)
 *
 */
public abstract class TaskIdentifier {
	
	private final TaskIdentifier mParentTaskIdentifier;
	
	protected abstract String getSubtaskIdentifier();
	
	
	
	public TaskIdentifier(final TaskIdentifier parentTaskIdentifier) {
		super();
		mParentTaskIdentifier = parentTaskIdentifier;
	}



	@Override
	public String toString() {
		if (mParentTaskIdentifier == null) {
			return getSubtaskIdentifier();
		} else {
			return mParentTaskIdentifier.toString() + "_" + getSubtaskIdentifier();
		}
	}

}
