/*
 * Copyright (C) 2023 Dominik Klumpp (klumpp@informatik.uni-freiburg.de)
 * Copyright (C) 2023 University of Freiburg
 *
 * This file is part of the ULTIMATE Proofs Library.
 *
 * The ULTIMATE Proofs Library is free software: you can redistribute it and/or modify
 * it under the terms of the GNU Lesser General Public License as published
 * by the Free Software Foundation, either version 3 of the License, or
 * (at your option) any later version.
 *
 * The ULTIMATE Proofs Library is distributed in the hope that it will be useful,
 * but WITHOUT ANY WARRANTY; without even the implied warranty of
 * MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
 * GNU Lesser General Public License for more details.
 *
 * You should have received a copy of the GNU Lesser General Public License
 * along with the ULTIMATE Proofs Library. If not, see <http://www.gnu.org/licenses/>.
 *
 * Additional permission under GNU GPL version 3 section 7:
 * If you modify the ULTIMATE Proofs Library, or any covered work, by linking
 * or combining it with Eclipse RCP (or a modified version of Eclipse RCP),
 * containing parts covered by the terms of the Eclipse Public License, the
 * licensors of the ULTIMATE Proofs Library grant you additional permission
 * to convey the resulting work.
 */
package de.uni_freiburg.informatik.ultimate.lib.proofs.floydhoare;

import java.util.HashMap;
import java.util.Set;
import java.util.function.Function;

import de.uni_freiburg.informatik.ultimate.automata.nestedword.INestedWordAutomaton;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.cfg.structure.IcfgLocation;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.smt.predicates.IPredicate;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.smt.predicates.PredicateUtils;

public class IcfgAnnotationFromAutomaton<S> {
	private final Function<S, IcfgLocation> mGetProgramPoint;
	private final IFloydHoareAnnotation<IcfgLocation> mResult;

	public IcfgAnnotationFromAutomaton(final IFloydHoareAnnotation<S> annotation, final Set<S> states,
			final Function<S, IcfgLocation> getProgramPoint) {
		mGetProgramPoint = getProgramPoint;
		mResult = extractAnnotation(annotation, states);
	}

	public static <S extends IPredicate> IcfgAnnotationFromAutomaton<S>
			create(final IFloydHoareAnnotation<S> automatonAnnotation, final Set<S> states) {
		return new IcfgAnnotationFromAutomaton<>(automatonAnnotation, states, PredicateUtils::getLocation);
	}

	public static <S extends IPredicate> IcfgAnnotationFromAutomaton<S>
			create(final IFloydHoareAnnotation<S> automatonAnnotation, final INestedWordAutomaton<?, S> automaton) {
		return new IcfgAnnotationFromAutomaton<>(automatonAnnotation, automaton.getStates(),
				PredicateUtils::getLocation);
	}

	private IFloydHoareAnnotation<IcfgLocation> extractAnnotation(final IFloydHoareAnnotation<S> annotation,
			final Set<S> states) {
		final var result = new HashMap<IcfgLocation, IPredicate>();

		for (final var state : states) {
			final IPredicate pred = annotation.getAnnotation(state);
			if (pred == null) {
				// there is no annotation for this state
				continue;
			}

			final var loc = mGetProgramPoint.apply(state);

			final var annot = result.get(loc);
			if (annot != null) {
				// TODO add the invariant, don't overwrite the old one
			}

			result.put(loc, pred);
		}

		return new FloydHoareMapping<>(annotation.getPrecondition(), annotation.getPostcondition(), result);
	}

	public IFloydHoareAnnotation<IcfgLocation> getResult() {
		return mResult;
	}
}
