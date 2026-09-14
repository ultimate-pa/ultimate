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

import java.util.List;

import de.uni_freiburg.informatik.ultimate.automata.petrinet.IPetriNet;
import de.uni_freiburg.informatik.ultimate.automata.petrinet.Marking;
import de.uni_freiburg.informatik.ultimate.automata.petrinet.PetriNetNot1SafeException;
import de.uni_freiburg.informatik.ultimate.core.model.services.IUltimateServiceProvider;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.cfg.ModifiableGlobalsTable;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.cfg.structure.IAction;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.cfg.structure.ICallAction;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.cfg.structure.IInternalAction;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.cfg.structure.IReturnAction;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.hoaretriple.MonolithicHoareTripleChecker;
import de.uni_freiburg.informatik.ultimate.lib.smtlibutils.ManagedScript;
import de.uni_freiburg.informatik.ultimate.util.datastructures.relation.Pair;
import de.uni_freiburg.informatik.ultimate.util.datastructures.relation.Triple;

/**
 * Checks validity of a Floyd/Hoare annotation for the reachability graph of a (1-safe) Petri net.
 *
 * @param <L>
 *            The type of letters in the net
 * @param <P>
 *            The type of places
 */
public class PetriFloydHoareValidityCheck<L extends IAction, P> extends FloydHoareValidityCheck<Marking<P>> {
	private static final String ONE_SAFE_ERROR = "Only 1-safe Petri nets are supported";
	private final IPetriNet<L, P> mProgram;

	public PetriFloydHoareValidityCheck(final IUltimateServiceProvider services, final ManagedScript mgdScript,
			final ModifiableGlobalsTable modifiableGlobals, final IPetriNet<L, P> program,
			final IFloydHoareAnnotation<Marking<P>> floydHoare) throws PetriNetNot1SafeException {
		super(services, mgdScript, new MonolithicHoareTripleChecker(mgdScript, modifiableGlobals), floydHoare, false,
				MissingAnnotationBehaviour.THROW, true);
		mProgram = program;
		try {
			performCheck();
		} catch (final IllegalArgumentException e) {
			if (ONE_SAFE_ERROR.equals(e.getMessage())) {
				throw (PetriNetNot1SafeException) e.getCause();
			}
			throw e;
		}
	}

	@Override
	protected Iterable<Pair<IInternalAction, Marking<P>>> getInternalSuccessors(final Marking<P> marking) {
		return () -> mProgram.getSuccessorTransitionProviders(marking.getPlaces(), marking.getPlaces()).stream()
				.flatMap(provider -> provider.getTransitions().stream()).map(transition -> {
					try {
						final var successor = marking.fireTransition(transition);
						return new Pair<>((IInternalAction) transition.getSymbol(), successor);
					} catch (final PetriNetNot1SafeException e) {
						throw new IllegalArgumentException(ONE_SAFE_ERROR, e);
					}
				}).iterator();
	}

	@Override
	protected Iterable<Pair<ICallAction, Marking<P>>> getCallSuccessors(final Marking<P> state) {
		return List.of();
	}

	@Override
	protected Iterable<Triple<IReturnAction, Marking<P>, Marking<P>>> getReturnSuccessors(final Marking<P> state) {
		return List.of();
	}
}
