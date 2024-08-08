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
import de.uni_freiburg.informatik.ultimate.automata.nestedword.INwaBasis;
import de.uni_freiburg.informatik.ultimate.automata.nestedword.NestedRun;
import de.uni_freiburg.informatik.ultimate.automata.nestedword.VpAlphabet;
import de.uni_freiburg.informatik.ultimate.core.model.services.IUltimateServiceProvider;
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

	public static boolean isEmptyStem(final NestedRun<?, ?> stem) {
		assert stem.getLength() > 0;
		return stem.getLength() == 1;
	}

	public static <LETTER> VpAlphabet<LETTER> getVpAlphabet(final IAutomaton<LETTER, ?> automaton) {
		if (automaton instanceof INwaBasis) {
			return ((INwaBasis<LETTER, ?>) automaton).getVpAlphabet();
		}
		return new VpAlphabet<>(automaton.getAlphabet());
	}
}
