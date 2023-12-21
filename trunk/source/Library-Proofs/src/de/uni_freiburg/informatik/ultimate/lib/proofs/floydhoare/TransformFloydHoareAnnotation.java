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
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.smt.predicates.ISLPredicate;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.smt.predicates.PredicateUtils;

/**
 * Transforms a Floyd-Hoare annotation by applying a function to every state.
 *
 * @author Dominik Klumpp (klumpp@informatik.uni-freiburg.de)
 *
 * @param <S1>
 *            The type of states of the given Floyd-Hoare annotation
 * @param <S2>
 *            The type of states of the transformed Floyd-Hoare annotation
 */
public class TransformFloydHoareAnnotation<S1, S2> {
	private final Function<S1, S2> mTransformer;
	private final IFloydHoareAnnotation<S2> mResult;

	/**
	 * Creates a new instance and transforms a given annotation
	 *
	 * @param annotation
	 *            The input annotation to be transformed
	 * @param states
	 *            The set of all states/locations to be transformed. Annotations for any state not included in this set
	 *            will be dropped.
	 * @param transformer
	 *            The function to be applied to each state (which must be injective)
	 */
	public TransformFloydHoareAnnotation(final IFloydHoareAnnotation<S1> annotation, final Set<S1> states,
			final Function<S1, S2> transformer) {
		mTransformer = transformer;
		mResult = extractAnnotation(annotation, states);
	}

	private static <S extends IPredicate> TransformFloydHoareAnnotation<S, IcfgLocation>
			predicateToIcfgLocation(final IFloydHoareAnnotation<S> automatonAnnotation, final Set<S> states) {
		return new TransformFloydHoareAnnotation<>(automatonAnnotation, states, PredicateUtils::getLocation);
	}

	/**
	 * Constructs a Floyd-Hoare annotation for a sequential ICFG from a Floyd-Hoare annotation for the corresponding
	 * nested-word automaton.
	 *
	 * @param <S>
	 *            The type of automaton states. In practice, all states must implement {@link ISLPredicate}.
	 * @param automatonAnnotation
	 *            The Floyd-Hoare annotation of the nested-word automaton
	 * @param automaton
	 *            The nested-word automaton
	 * @return a Floyd-Hoare annotation for the ICFG
	 */
	public static <S extends IPredicate> IFloydHoareAnnotation<IcfgLocation>
			nwaToIcfg(final IFloydHoareAnnotation<S> automatonAnnotation, final INestedWordAutomaton<?, S> automaton) {
		return predicateToIcfgLocation(automatonAnnotation, automaton.getStates()).getResult();
	}

	private IFloydHoareAnnotation<S2> extractAnnotation(final IFloydHoareAnnotation<S1> annotation,
			final Set<S1> states) {
		final var result = new HashMap<S2, IPredicate>();

		for (final S1 state : states) {
			final IPredicate pred = annotation.getAnnotation(state);
			if (pred == null) {
				// there is no annotation for this state
				continue;
			}

			final var transformed = mTransformer.apply(state);
			final var annot = result.get(transformed);
			if (annot != null) {
				throw new IllegalStateException(
						"two different annotations for " + transformed + ": " + annot + " and " + pred);
			}

			result.put(transformed, pred);
		}
		return new FloydHoareMapping<>(annotation.getPrecondition(), annotation.getPostcondition(), result);
	}

	public IFloydHoareAnnotation<S2> getResult() {
		return mResult;
	}
}
