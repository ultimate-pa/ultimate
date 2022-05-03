/*
 * Copyright (C) 2014-2015 Daniel Dietsch (dietsch@informatik.uni-freiburg.de)
 * Copyright (C) 2013-2015 Matthias Heizmann (heizmann@informatik.uni-freiburg.de)
 * Copyright (C) 2022 Frank Schüssele (schuessf@informatik.uni-freiburg.de)
 * Copyright (C) 2022 University of Freiburg
 *
 * This file is part of the ULTIMATE BuchiAutomizer plug-in.
 *
 * The ULTIMATE BuchiAutomizer plug-in is free software: you can redistribute it and/or modify
 * it under the terms of the GNU Lesser General Public License as published
 * by the Free Software Foundation, either version 3 of the License, or
 * (at your option) any later version.
 *
 * The ULTIMATE BuchiAutomizer plug-in is distributed in the hope that it will be useful,
 * but WITHOUT ANY WARRANTY; without even the implied warranty of
 * MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
 * GNU Lesser General Public License for more details.
 *
 * You should have received a copy of the GNU Lesser General Public License
 * along with the ULTIMATE BuchiAutomizer plug-in. If not, see <http://www.gnu.org/licenses/>.
 *
 * Additional permission under GNU GPL version 3 section 7:
 * If you modify the ULTIMATE BuchiAutomizer plug-in, or any covered work, by linking
 * or combining it with Eclipse RCP (or a modified version of Eclipse RCP),
 * containing parts covered by the terms of the Eclipse Public License, the
 * licensors of the ULTIMATE BuchiAutomizer plug-in grant you additional permission
 * to convey the resulting work.
 */

package de.uni_freiburg.informatik.ultimate.plugins.generator.buchiautomizer;

import de.uni_freiburg.informatik.ultimate.automata.AutomataLibraryServices;
import de.uni_freiburg.informatik.ultimate.automata.AutomatonDefinitionPrinter;
import de.uni_freiburg.informatik.ultimate.automata.AutomatonDefinitionPrinter.Format;
import de.uni_freiburg.informatik.ultimate.automata.IAutomaton;
import de.uni_freiburg.informatik.ultimate.automata.nestedword.INwaOutgoingLetterAndTransitionProvider;
import de.uni_freiburg.informatik.ultimate.automata.nestedword.NestedWord;
import de.uni_freiburg.informatik.ultimate.automata.nestedword.NestedWordAutomaton;
import de.uni_freiburg.informatik.ultimate.automata.nestedword.buchi.NestedLassoRun;
import de.uni_freiburg.informatik.ultimate.automata.statefactory.IEmptyStackStateFactory;
import de.uni_freiburg.informatik.ultimate.core.model.services.IUltimateServiceProvider;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.cfg.structure.IIcfgTransition;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.smt.predicates.IPredicate;

/**
 * @author Matthias Heizmann (heizmann@informatik.uni-freiburg.de)
 * @author Daniel Dietsch (dietsch@informatik.uni-freiburg.de)
 * @author Frank Schüssele (schuessf@informatik.uni-freiburg.de)
 */
public final class BuchiAutomizerUtils {
	private BuchiAutomizerUtils() {
	}

	public static void writeAutomatonToFile(final IUltimateServiceProvider services,
			final IAutomaton<?, IPredicate> automaton, final String path, final String filename, final Format format,
			final String message) {
		new AutomatonDefinitionPrinter<String, String>(new AutomataLibraryServices(services), "nwa",
				path + "/" + filename, format, message, automaton);
	}

	public static boolean isEmptyStem(final NestedLassoRun<?, IPredicate> nlr) {
		assert nlr.getStem().getLength() > 0;
		return nlr.getStem().getLength() == 1;
	}

	public static <LETTER extends IIcfgTransition<?>> NestedWordAutomaton<LETTER, IPredicate>
			constructBuchiInterpolantAutomaton(final IPredicate precondition, final NestedWord<LETTER> stem,
					final IPredicate[] stemInterpolants, final IPredicate honda, final NestedWord<LETTER> loop,
					final IPredicate[] loopInterpolants,
					final INwaOutgoingLetterAndTransitionProvider<LETTER, IPredicate> abstraction,
					final IUltimateServiceProvider services,
					final IEmptyStackStateFactory<IPredicate> emptyStateFactory) {
		final NestedWordAutomaton<LETTER, IPredicate> result = new NestedWordAutomaton<>(
				new AutomataLibraryServices(services), abstraction.getVpAlphabet(), emptyStateFactory);
		if (stem.length() == 0) {
			result.addState(true, true, honda);
		} else {
			result.addState(true, false, precondition);
			for (int i = 0; i < stemInterpolants.length; i++) {
				addState(stemInterpolants[i], result);
				addTransition(i, precondition, stemInterpolants, honda, stem, result);
			}
			result.addState(false, true, honda);
			addTransition(stemInterpolants.length, precondition, stemInterpolants, honda, stem, result);
		}
		for (int i = 0; i < loopInterpolants.length; i++) {
			addState(loopInterpolants[i], result);
			addTransition(i, honda, loopInterpolants, honda, loop, result);
		}
		addTransition(loopInterpolants.length, honda, loopInterpolants, honda, loop, result);
		return result;
	}

	private static void addState(final IPredicate pred, final NestedWordAutomaton<?, IPredicate> nwa) {
		if (!nwa.getStates().contains(pred)) {
			nwa.addState(false, false, pred);
		}
	}

	private static <LETTER extends IIcfgTransition<?>> void addTransition(final int pos, final IPredicate pre,
			final IPredicate[] predicates, final IPredicate post, final NestedWord<LETTER> nw,
			final NestedWordAutomaton<LETTER, IPredicate> nwa) {
		final IPredicate pred = getPredicateAtPosition(pos - 1, pre, predicates, post);
		final IPredicate succ = getPredicateAtPosition(pos, pre, predicates, post);
		final LETTER cb = nw.getSymbol(pos);
		if (nw.isInternalPosition(pos)) {
			nwa.addInternalTransition(pred, cb, succ);
		} else if (nw.isCallPosition(pos)) {
			nwa.addCallTransition(pred, cb, succ);
		} else if (nw.isReturnPosition(pos)) {
			assert !nw.isPendingReturn(pos);
			final int k = nw.getCallPosition(pos);
			final IPredicate hier = getPredicateAtPosition(k - 1, pre, predicates, post);
			nwa.addReturnTransition(pred, hier, cb, succ);
		}
	}

	private static IPredicate getPredicateAtPosition(final int pos, final IPredicate before,
			final IPredicate[] predicates, final IPredicate after) {
		assert pos >= -1;
		assert pos <= predicates.length;
		if (pos < 0) {
			return before;
		}
		if (pos >= predicates.length) {
			return after;
		}
		return predicates[pos];
	}
}
