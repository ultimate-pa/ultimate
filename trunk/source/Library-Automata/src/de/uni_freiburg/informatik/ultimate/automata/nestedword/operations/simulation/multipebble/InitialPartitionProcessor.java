/*
 * Copyright (C) 2017 Matthias Heizmann (heizmann@informatik.uni-freiburg.de)
 * Copyright (C) 2017 University of Freiburg
 * 
 * This file is part of the ULTIMATE Automata Library.
 * 
 * The ULTIMATE Automata Library is free software: you can redistribute it and/or modify
 * it under the terms of the GNU Lesser General Public License as published
 * by the Free Software Foundation, either version 3 of the License, or
 * (at your option) any later version.
 * 
 * The ULTIMATE Automata Library is distributed in the hope that it will be useful,
 * but WITHOUT ANY WARRANTY; without even the implied warranty of
 * MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
 * GNU Lesser General Public License for more details.
 * 
 * You should have received a copy of the GNU Lesser General Public License
 * along with the ULTIMATE Automata Library. If not, see <http://www.gnu.org/licenses/>.
 * 
 * Additional permission under GNU GPL version 3 section 7:
 * If you modify the ULTIMATE Automata Library, or any covered work, by linking
 * or combining it with Eclipse RCP (or a modified version of Eclipse RCP),
 * containing parts covered by the terms of the Eclipse Public License, the
 * licensors of the ULTIMATE Automata Library grant you additional permission
 * to convey the resulting work.
 */
package de.uni_freiburg.informatik.ultimate.automata.nestedword.operations.simulation.multipebble;

import java.util.Collection;
import java.util.Set;

import de.uni_freiburg.informatik.ultimate.automata.AutomataLibraryServices;
import de.uni_freiburg.informatik.ultimate.automata.AutomataOperationCanceledException;
import de.uni_freiburg.informatik.ultimate.automata.nestedword.NestedWordAutomataUtils;
import de.uni_freiburg.informatik.ultimate.core.lib.exceptions.RunningTaskInfo;

/**
 * @author Matthias Heizmann (heizmann@informatik.uni-freiburg.de)
 * @param <STATE>
 *            state type
 */
public abstract class InitialPartitionProcessor<STATE> {

	private final AutomataLibraryServices mServices;

	public InitialPartitionProcessor(final AutomataLibraryServices services) {
		mServices = services;
	}

	public abstract boolean shouldBeProcessed(STATE q0, STATE q1);

	public abstract void doProcess(STATE q0, STATE q1);

	public void process(final Collection<Set<STATE>> equivalenceClasses) throws AutomataOperationCanceledException {
		for (final Set<STATE> eqClass : equivalenceClasses) {
			if (!mServices.getProgressAwareTimer().continueProcessing()) {
				final long initialNodes = NestedWordAutomataUtils.computeNumberOfPairsInPartition(equivalenceClasses);
				final RunningTaskInfo rti =
						new RunningTaskInfo(getClass(), "constructing " + initialNodes + "initial vertices");
				throw new AutomataOperationCanceledException(rti);
			}
			for (final STATE q0 : eqClass) {
				for (final STATE q1 : eqClass) {
					if (shouldBeProcessed(q0, q1)) {
						doProcess(q0, q1);
					}
				}
			}
		}
	}

}
