/*
 * Copyright (C) 2016 Matthias Heizmann (heizmann@informatik.uni-freiburg.de)
 * Copyright (C) 2016 University of Freiburg
 *
 * This file is part of the ULTIMATE TraceAbstraction plug-in.
 *
 * The ULTIMATE TraceAbstraction plug-in is free software: you can redistribute it and/or modify
 * it under the terms of the GNU Lesser General Public License as published
 * by the Free Software Foundation, either version 3 of the License, or
 * (at your option) any later version.
 *
 * The ULTIMATE TraceAbstraction plug-in is distributed in the hope that it will be useful,
 * but WITHOUT ANY WARRANTY; without even the implied warranty of
 * MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE. See the
 * GNU Lesser General Public License for more details.
 *
 * You should have received a copy of the GNU Lesser General Public License
 * along with the ULTIMATE TraceAbstraction plug-in. If not, see <http://www.gnu.org/licenses/>.
 *
 * Additional permission under GNU GPL version 3 section 7:
 * If you modify the ULTIMATE TraceAbstraction plug-in, or any covered work, by linking
 * or combining it with Eclipse RCP (or a modified version of Eclipse RCP),
 * containing parts covered by the terms of the Eclipse Public License, the
 * licensors of the ULTIMATE TraceAbstraction plug-in grant you additional permission
 * to convey the resulting work.
 */
package de.uni_freiburg.informatik.ultimate.plugins.generator.traceabstraction.tracehandling;

import java.util.Collections;

import de.uni_freiburg.informatik.ultimate.automata.Word;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.cfg.structure.IAction;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.cfg.structure.ICallAction;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.cfg.structure.IInternalAction;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.cfg.structure.IReturnAction;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.smt.ContainsSort;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.smt.predicates.IPredicate;
import de.uni_freiburg.informatik.ultimate.plugins.generator.traceabstraction.preferences.TraceAbstractionPreferenceInitializer.RefinementStrategy;

/**
 * Provides static auxiliary methods for {@link RefinementStrategy}s.
 *
 * @author Matthias Heizmann (heizmann@informatik.uni-freiburg.de)
 */
public class RefinementStrategyUtils {
	
	public static final String NAME_OF_FLOAT_SORT = "FloatingPoint";
	
	private RefinementStrategyUtils() {
	}

	/**
	 * Returns true iff word contains some float variable.
	 * @param iPredicate 
	 */
	public static boolean containsFloats(final Word<? extends IAction> word, final IPredicate axioms) {
		
		final ContainsSort cs = new ContainsSort(Collections.singleton(NAME_OF_FLOAT_SORT));
		boolean containsFloats = false;
		containsFloats |= cs.containsSubtermOfGivenSort(axioms.getFormula());
		if (containsFloats) {
			return true;
		}
		for (final IAction action : word) {
			if (action instanceof IInternalAction) {
				containsFloats |= cs.containsSubtermOfGivenSort(((IInternalAction) action).getTransformula().getFormula());
				if (containsFloats) {
					return true;
				}
			} else if (action instanceof ICallAction) {
				containsFloats |= cs.containsSubtermOfGivenSort(((ICallAction) action).getLocalVarsAssignment().getFormula());
				if (containsFloats) {
					return true;
				}
			} else if (action instanceof IReturnAction) {
				containsFloats |= cs.containsSubtermOfGivenSort(((IReturnAction) action).getAssignmentOfReturn().getFormula());
				if (containsFloats) {
					return true;
				}
			}
		}
		return false;
	}

}
