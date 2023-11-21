/*
 * Copyright (C) 2023 Dominik Klumpp (klumpp@informatik.uni-freiburg.de)
 * Copyright (C) 2023 University of Freiburg
 *
 * This file is part of the ULTIMATE TraceCheckerUtils Library.
 *
 * The ULTIMATE TraceCheckerUtils Library is free software: you can redistribute it and/or modify
 * it under the terms of the GNU Lesser General Public License as published
 * by the Free Software Foundation, either version 3 of the License, or
 * (at your option) any later version.
 *
 * The ULTIMATE TraceCheckerUtils Library is distributed in the hope that it will be useful,
 * but WITHOUT ANY WARRANTY; without even the implied warranty of
 * MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
 * GNU Lesser General Public License for more details.
 *
 * You should have received a copy of the GNU Lesser General Public License
 * along with the ULTIMATE TraceCheckerUtils Library. If not, see <http://www.gnu.org/licenses/>.
 *
 * Additional permission under GNU GPL version 3 section 7:
 * If you modify the ULTIMATE TraceCheckerUtils Library, or any covered work, by linking
 * or combining it with Eclipse RCP (or a modified version of Eclipse RCP),
 * containing parts covered by the terms of the Eclipse Public License, the
 * licensors of the ULTIMATE TraceCheckerUtils Library grant you additional permission
 * to convey the resulting work.
 */
package de.uni_freiburg.informatik.ultimate.lib.tracecheckerutils.owickigries;

import java.util.ArrayDeque;
import java.util.HashSet;
import java.util.List;
import java.util.Map;
import java.util.stream.Collectors;

import de.uni_freiburg.informatik.ultimate.automata.petrinet.IPetriNet;
import de.uni_freiburg.informatik.ultimate.automata.petrinet.Marking;
import de.uni_freiburg.informatik.ultimate.automata.petrinet.PetriNetNot1SafeException;
import de.uni_freiburg.informatik.ultimate.automata.petrinet.netdatastructures.Transition;
import de.uni_freiburg.informatik.ultimate.core.model.services.ILogger;
import de.uni_freiburg.informatik.ultimate.core.model.services.IUltimateServiceProvider;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.cfg.IIcfgSymbolTable;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.cfg.ModifiableGlobalsTable;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.cfg.structure.IAction;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.cfg.structure.IInternalAction;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.hoaretriple.IHoareTripleChecker;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.hoaretriple.MonolithicHoareTripleChecker;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.smt.predicates.BasicPredicateFactory;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.smt.predicates.IPredicate;
import de.uni_freiburg.informatik.ultimate.lib.smtlibutils.IncrementalPlicationChecker.Validity;
import de.uni_freiburg.informatik.ultimate.lib.smtlibutils.ManagedScript;
import de.uni_freiburg.informatik.ultimate.util.datastructures.ImmutableSet;

public class PetriFloydHoareValidityCheck<L extends IAction, P> {
	private final ILogger mLogger;
	private final IHoareTripleChecker mHtc;
	private final BasicPredicateFactory mPredicateFactory;

	private final IPetriNet<L, P> mProgram;
	private final Map<Marking<P>, IPredicate> mAnnotation;

	private final Validity mResult;

	public PetriFloydHoareValidityCheck(final IUltimateServiceProvider services, final ManagedScript mgdScript,
			final IIcfgSymbolTable symbolTable, final ModifiableGlobalsTable modifiableGlobals,
			final IPetriNet<L, P> program, final Map<Marking<P>, IPredicate> floydHoare)
			throws PetriNetNot1SafeException {
		mLogger = services.getLoggingService().getLogger(getClass());
		mHtc = new MonolithicHoareTripleChecker(mgdScript, modifiableGlobals);
		mPredicateFactory = new BasicPredicateFactory(services, mgdScript, symbolTable);

		mProgram = program;
		mAnnotation = floydHoare;

		// TODO check initial marking is annotated with true
		// TODO check all error markings are annotated with false
		mResult = checkInductivity(new Marking<>(ImmutableSet.of(program.getInitialPlaces())));
	}

	private Validity checkInductivity(final Marking<P> initial) throws PetriNetNot1SafeException {
		final var worklist = new ArrayDeque<Marking<P>>();
		worklist.add(initial);

		final var visited = new HashSet<Marking<P>>();
		var result = Validity.VALID;

		while (!worklist.isEmpty()) {
			final var markPre = worklist.poll();
			if (!visited.add(markPre)) {
				continue;
			}

			final var pre = getAnnotation(markPre);
			for (final var trans : getEnabledTransitions(markPre)) {
				final var markPost = markPre.fireTransition(trans);

				final var check = checkInductivity(markPre, pre, trans, markPost);
				result = result.and(check);
				if (result == Validity.INVALID) {
					return result;
				}

				worklist.offer(markPost);
			}
		}

		return result;
	}

	private Validity checkInductivity(final Marking<P> markPre, final IPredicate pre, final Transition<L, P> trans,
			final Marking<P> markPost) {
		final var post = getAnnotation(markPost);
		final Validity valid = mHtc.checkInternal(pre, (IInternalAction) trans.getSymbol(), post);
		if (valid != Validity.VALID) {
			mLogger.error("Non-inductive transition.\n"
					+ "\tprecondition: %s\n\tpre-marking: %s\n\ttransition: %s\n\tpostcondition: %s\n\tpost-marking: %s",
					pre, markPre, trans, post, markPost);
		}
		return valid;
	}

	private List<Transition<L, P>> getEnabledTransitions(final Marking<P> marking) {
		return mProgram.getTransitions().stream().filter(marking::isTransitionEnabled).collect(Collectors.toList());
	}

	private IPredicate getAnnotation(final Marking<P> marking) {
		final var predicate = mAnnotation.get(marking);
		if (predicate != null) {
			return predicate;
		}
		mLogger.warn("Using annotation false for marking without entry: %s", marking);
		return mPredicateFactory.or();
	}

	public Validity isValid() {
		return mResult;
	}
}
