/*
 * Copyright (C) 2019 Daniel Dietsch (dietsch@informatik.uni-freiburg.de)
 * Copyright (C) 2019 University of Freiburg
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

import java.util.List;

import de.uni_freiburg.informatik.ultimate.automata.AutomataOperationCanceledException;
import de.uni_freiburg.informatik.ultimate.automata.IAutomaton;
import de.uni_freiburg.informatik.ultimate.automata.IRun;
import de.uni_freiburg.informatik.ultimate.automata.nestedword.INestedWordAutomaton;
import de.uni_freiburg.informatik.ultimate.automata.nestedword.NestedRun;
import de.uni_freiburg.informatik.ultimate.automata.nestedword.NestedWordAutomaton;
import de.uni_freiburg.informatik.ultimate.core.model.services.IUltimateServiceProvider;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.cfg.CfgSmtToolkit;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.cfg.structure.IIcfgTransition;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.smt.SmtUtils.SimplificationTechnique;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.smt.SmtUtils.XnfConversionTechnique;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.smt.interpolant.TracePredicates;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.smt.predicates.IPredicate;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.smt.predicates.IPredicateUnifier;
import de.uni_freiburg.informatik.ultimate.plugins.generator.traceabstraction.PredicateFactoryForInterpolantAutomata;
import de.uni_freiburg.informatik.ultimate.plugins.generator.traceabstraction.interpolantautomata.builders.TotalInterpolationAutomatonBuilder;
import de.uni_freiburg.informatik.ultimate.plugins.generator.traceabstraction.preferences.TraceAbstractionPreferenceInitializer.InterpolationTechnique;

/**
 * @author Daniel Dietsch (dietsch@informatik.uni-freiburg.de)
 *
 * @param <LETTER>
 */
public class IpAbStrategyModuleTotalInterpolation<LETTER extends IIcfgTransition<?>>
		implements IIpAbStrategyModule<LETTER> {

	private final IUltimateServiceProvider mServices;
	private final IRun<LETTER, IPredicate, ?> mCounterexample;
	private final IAutomaton<LETTER, IPredicate> mAbstraction;
	private final IPredicateUnifier mPredicateUnifier;
	private final PredicateFactoryForInterpolantAutomata mPredicateFactory;
	private final CfgSmtToolkit mCsToolkit;
	private final InterpolationTechnique mInterpolationTechnique;

	private NestedWordAutomaton<LETTER, IPredicate> mAutomaton;

	public IpAbStrategyModuleTotalInterpolation(
			final IUltimateServiceProvider services, final IAutomaton<LETTER, IPredicate> abstraction,
			final IRun<LETTER, IPredicate, ?> counterexample, final IPredicateUnifier predicateUnifier,
			final TaCheckAndRefinementPreferences<LETTER> prefs, final CfgSmtToolkit csToolkit,
			final PredicateFactoryForInterpolantAutomata predFac) {
		mServices = services;
		mAbstraction = abstraction;
		mCounterexample = counterexample;
		mPredicateUnifier = predicateUnifier;
		mInterpolationTechnique = prefs.getInterpolationTechnique();
		mCsToolkit = csToolkit;
		mPredicateFactory = predFac;
	}

	@Override
	public NestedWordAutomaton<LETTER, IPredicate> buildInterpolantAutomaton(final List<TracePredicates> perfectIpps,
			final List<TracePredicates> imperfectIpps) throws AutomataOperationCanceledException {
		if (mAutomaton == null) {
			if (perfectIpps.isEmpty() && imperfectIpps.isEmpty()) {
				throw new AssertionError();
			}
			final TracePredicates ipp;
			if (!perfectIpps.isEmpty()) {
				ipp = perfectIpps.get(0);
			} else {
				ipp = imperfectIpps.get(0);
			}
			final INestedWordAutomaton<LETTER, IPredicate> castedAbstraction =
					(INestedWordAutomaton<LETTER, IPredicate>) mAbstraction;
			@SuppressWarnings("unchecked")
			final NestedRun<LETTER, IPredicate> castedCex = (NestedRun<LETTER, IPredicate>) mCounterexample;
			mAutomaton = new TotalInterpolationAutomatonBuilder<>(castedAbstraction, castedCex, mCsToolkit,
					mPredicateFactory, mInterpolationTechnique, mServices, SimplificationTechnique.SIMPLIFY_DDA,
					XnfConversionTechnique.BOTTOM_UP_WITH_LOCAL_SIMPLIFICATION, false, mPredicateUnifier, ipp)
							.getResult();
		}
		return mAutomaton;
	}

}
