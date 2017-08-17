/*
 * Copyright (C) 2017 Christian Schilling (schillic@informatik.uni-freiburg.de)
 * Copyright (C) 2017 University of Freiburg
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
package de.uni_freiburg.informatik.ultimate.plugins.generator.traceabstraction.errorabstraction;

import de.uni_freiburg.informatik.ultimate.automata.nestedword.INwaOutgoingLetterAndTransitionProvider;
import de.uni_freiburg.informatik.ultimate.automata.nestedword.NestedWordAutomaton;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.cfg.structure.IIcfgTransition;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.smt.predicates.IPredicate;
import de.uni_freiburg.informatik.ultimate.plugins.generator.traceabstraction.preferences.TAPreferences.InterpolantAutomatonEnhancement;

/**
 * Creates an error automaton which is a generalization of an error trace.
 * 
 * @author Christian Schilling (schillic@informatik.uni-freiburg.de)
 * @param <LETTER>
 *            letter type
 */
public interface IErrorAutomatonBuilder<LETTER extends IIcfgTransition<?>> {
	/**
	 * Type of automaton that is constructed.
	 * 
	 * @author Christian Schilling (schillic@informatik.uni-freiburg.de)
	 */
	public enum ErrorAutomatonType {
		/**
		 * Error automaton.
		 */
		ERROR_AUTOMATON,
		/**
		 * Danger automaton.
		 */
		DANGER_AUTOMATON
	}

	/**
	 * @return Raw automaton before (on-demand) enhancement.
	 */
	NestedWordAutomaton<LETTER, IPredicate> getResultBeforeEnhancement();

	/**
	 * @return Automaton after (on-demand) enhancement. The additional transitions are not explicitly added. They will
	 *         be computed when asking for successors.
	 */
	INwaOutgoingLetterAndTransitionProvider<LETTER, IPredicate> getResultAfterEnhancement();

	/**
	 * @return Type of error automaton.
	 */
	ErrorAutomatonType getType();

	/**
	 * @return Error precondition (may be {@code null}).
	 */
	IPredicate getErrorPrecondition();

	/**
	 * @return Enhancement mode.
	 */
	InterpolantAutomatonEnhancement getEnhancementMode();
}
