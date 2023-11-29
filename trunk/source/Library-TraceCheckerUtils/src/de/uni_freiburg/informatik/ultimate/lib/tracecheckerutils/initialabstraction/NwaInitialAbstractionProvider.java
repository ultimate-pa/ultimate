/*
 * Copyright (C) 2022 Dominik Klumpp (klumpp@informatik.uni-freiburg.de)
 * Copyright (C) 2022 University of Freiburg
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
package de.uni_freiburg.informatik.ultimate.lib.tracecheckerutils.initialabstraction;

import java.util.Set;

import de.uni_freiburg.informatik.ultimate.automata.nestedword.INestedWordAutomaton;
import de.uni_freiburg.informatik.ultimate.automata.statefactory.IEmptyStackStateFactory;
import de.uni_freiburg.informatik.ultimate.core.model.services.IUltimateServiceProvider;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.cfg.structure.IIcfg;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.cfg.structure.IIcfgTransition;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.cfg.structure.IcfgLocation;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.proofs.IProofConverter;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.proofs.IProofProducer;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.smt.predicates.IPredicate;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.smt.predicates.PredicateFactory;
import de.uni_freiburg.informatik.ultimate.lib.tracecheckerutils.cfg2automaton.Cfg2Automaton;
import de.uni_freiburg.informatik.ultimate.lib.tracecheckerutils.floydhoare.IFloydHoareAnnotation;

/**
 * Provides an initial abstraction in the form of a nested word automaton. This is only applicable to sequential
 * programs.
 *
 * @author Dominik Klumpp (klumpp@informatik.uni-freiburg.de)
 *
 * @param <L>
 *            The type of transitions
 */
public class NwaInitialAbstractionProvider<L extends IIcfgTransition<?>>
		implements IInitialAbstractionProvider<L, INestedWordAutomaton<L, IPredicate>> {

	private final IUltimateServiceProvider mServices;
	private final IEmptyStackStateFactory<IPredicate> mStateFactory;
	private final boolean mInterprocedural;
	private final PredicateFactory mPredicateFactory;

	private INestedWordAutomaton<L, IPredicate> mAbstraction;

	/**
	 * Create a new instance. For documentation of the parameters, see the corresponding parameters in
	 * {@link CFG2NestedWordAutomaton#constructAutomatonWithSPredicates(IUltimateServiceProvider, IIcfg, IEmptyStackStateFactory, java.util.Collection, boolean, PredicateFactory)}.
	 */
	public NwaInitialAbstractionProvider(final IUltimateServiceProvider services,
			final IEmptyStackStateFactory<IPredicate> stateFactory, final boolean interprocedural,
			final PredicateFactory predicateFactory // ,
	// TODO: Add HoareAnnotationPositions.NONE in place of this boolean
	// final boolean computeHoareAnnotation, final HoareAnnotationPositions hoarePositions
	) {
		mServices = services;
		mStateFactory = stateFactory;
		mInterprocedural = interprocedural;
		mPredicateFactory = predicateFactory;
	}

	@Override
	public INestedWordAutomaton<L, IPredicate> getInitialAbstraction(final IIcfg<? extends IcfgLocation> icfg,
			final Set<? extends IcfgLocation> errorLocs) {
		if (mAbstraction == null) {
			mAbstraction = Cfg2Automaton.constructAutomatonWithSPredicates(mServices, icfg, mStateFactory, errorLocs,
					mInterprocedural, mPredicateFactory);
		}
		return mAbstraction;
	}

	@Override
	public <PROOF> IProofProducer<INestedWordAutomaton<L, IPredicate>, PROOF>
			getProofProducer(final Class<PROOF> proofType, final Class<?> proofUpdates) {
		if (proofUpdates == null || proofUpdates.isAssignableFrom(NwaHoareProofProducer.class)) {
			// TODO implement retrieval of suitable proof converter, if one exists
			final IProofConverter<INestedWordAutomaton<L, IPredicate>, IFloydHoareAnnotation<L, IPredicate>, PROOF> converter =
					null;

			if (converter != null) {
				return NwaHoareProofProducer.create(mAbstraction).withPostProcessor(converter);
			}
		}

		return IInitialAbstractionProvider.super.getProofProducer(proofType, proofUpdates);
	}
}
