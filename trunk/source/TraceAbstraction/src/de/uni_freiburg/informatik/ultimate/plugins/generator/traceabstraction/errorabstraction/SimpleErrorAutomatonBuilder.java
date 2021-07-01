/*
 * Copyright (C) 2021 Daniel Dietsch (dietsch@informatik.uni-freiburg.de)
 * Copyright (C) 2021 University of Freiburg
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

import de.uni_freiburg.informatik.ultimate.automata.AutomataLibraryServices;
import de.uni_freiburg.informatik.ultimate.automata.nestedword.INestedWordAutomaton;
import de.uni_freiburg.informatik.ultimate.automata.nestedword.INwaOutgoingLetterAndTransitionProvider;
import de.uni_freiburg.informatik.ultimate.automata.nestedword.NestedWord;
import de.uni_freiburg.informatik.ultimate.automata.nestedword.NestedWordAutomataUtils;
import de.uni_freiburg.informatik.ultimate.automata.nestedword.NestedWordAutomaton;
import de.uni_freiburg.informatik.ultimate.automata.nestedword.VpAlphabet;
import de.uni_freiburg.informatik.ultimate.core.model.services.IUltimateServiceProvider;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.cfg.CfgSmtToolkit;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.cfg.structure.IIcfgTransition;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.smt.predicates.IPredicate;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.smt.predicates.IPredicateUnifier;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.smt.predicates.PredicateFactory;
import de.uni_freiburg.informatik.ultimate.plugins.generator.traceabstraction.PredicateFactoryForInterpolantAutomata;
import de.uni_freiburg.informatik.ultimate.plugins.generator.traceabstraction.preferences.TAPreferences.InterpolantAutomatonEnhancement;

/**
 *
 * @author Daniel Dietsch (dietsch@informatik.uni-freiburg.de)
 *
 * @param <L>
 */
public class SimpleErrorAutomatonBuilder<L extends IIcfgTransition<?>> implements IErrorAutomatonBuilder<L> {

	private final NestedWordAutomaton<L, IPredicate> mResult;
	private final IPredicate mTruePredicate;

	public SimpleErrorAutomatonBuilder(final IUltimateServiceProvider services, final PredicateFactory predicateFactory,
			final IPredicateUnifier predicateUnifier, final CfgSmtToolkit csToolkit,
			final PredicateFactoryForInterpolantAutomata predicateFactoryErrorAutomaton,
			final INestedWordAutomaton<L, IPredicate> abstraction, final NestedWord<L> trace) {
		mTruePredicate = predicateUnifier.getTruePredicate();
		mResult = constructStraightLineAutomaton(services, csToolkit, predicateFactory, predicateUnifier,
				predicateFactoryErrorAutomaton, NestedWordAutomataUtils.getVpAlphabet(abstraction), trace);
	}

	private NestedWordAutomaton<L, IPredicate> constructStraightLineAutomaton(final IUltimateServiceProvider services,
			final CfgSmtToolkit csToolkit, final PredicateFactory predicateFactory,
			final IPredicateUnifier predicateUnifier,
			final PredicateFactoryForInterpolantAutomata predicateFactoryInterpolantAutomata,
			final VpAlphabet<L> alphabet, final NestedWord<L> trace) throws AssertionError {
		final IPredicate initTrue = predicateUnifier.getTruePredicate();
		final IPredicate finalTrue =
				predicateFactory.newPredicate(csToolkit.getManagedScript().getScript().term("true"));

		final NestedWordAutomaton<L, IPredicate> nwa = new NestedWordAutomaton<>(new AutomataLibraryServices(services),
				alphabet, predicateFactoryInterpolantAutomata);

		nwa.addState(true, false, initTrue);
		nwa.addState(false, true, finalTrue);
		final L lastLetter = trace.getSymbol(trace.length() - 1);
		nwa.addInternalTransition(initTrue, lastLetter, finalTrue);

		// add self loops
		nwa.addInternalTransition(finalTrue, lastLetter, finalTrue);
		alphabet.getInternalAlphabet().stream().filter(a -> a != lastLetter).forEach(a -> {
			nwa.addInternalTransition(initTrue, a, initTrue);
			nwa.addInternalTransition(finalTrue, a, finalTrue);
		});
		alphabet.getCallAlphabet().stream().forEach(a -> {
			nwa.addCallTransition(initTrue, a, initTrue);
			nwa.addCallTransition(finalTrue, a, finalTrue);
		});
		alphabet.getReturnAlphabet().stream().forEach(a -> {
			nwa.addReturnTransition(initTrue, initTrue, a, initTrue);
			nwa.addReturnTransition(finalTrue, finalTrue, a, finalTrue);
		});

		return nwa;
	}

	@Override
	public NestedWordAutomaton<L, IPredicate> getResultBeforeEnhancement() {
		return mResult;
	}

	@Override
	public INwaOutgoingLetterAndTransitionProvider<L, IPredicate> getResultAfterEnhancement() {
		return mResult;
	}

	@Override
	public ErrorAutomatonType getType() {
		return ErrorAutomatonType.SIMPLE_ERROR_AUTOMATON;
	}

	@Override
	public IPredicate getErrorPrecondition() {
		return mTruePredicate;
	}

	@Override
	public InterpolantAutomatonEnhancement getEnhancementMode() {
		return InterpolantAutomatonEnhancement.NONE;
	}

}
