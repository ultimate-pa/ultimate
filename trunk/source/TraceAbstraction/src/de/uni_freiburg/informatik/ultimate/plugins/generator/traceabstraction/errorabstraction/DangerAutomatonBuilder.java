/*
 * Copyright (C) 2017 Christian Schilling (schillic@informatik.uni-freiburg.de)
 * Copyright (C) 2017 Matthias Heizmann (heizmann@informatik.uni-freiburg.de)
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

import java.util.Deque;
import java.util.HashMap;
import java.util.HashSet;
import java.util.LinkedList;
import java.util.Map;
import java.util.Set;

import de.uni_freiburg.informatik.ultimate.automata.AutomataLibraryServices;
import de.uni_freiburg.informatik.ultimate.automata.nestedword.INestedWordAutomaton;
import de.uni_freiburg.informatik.ultimate.automata.nestedword.INwaOutgoingLetterAndTransitionProvider;
import de.uni_freiburg.informatik.ultimate.automata.nestedword.NestedWord;
import de.uni_freiburg.informatik.ultimate.automata.nestedword.NestedWordAutomaton;
import de.uni_freiburg.informatik.ultimate.automata.nestedword.VpAlphabet;
import de.uni_freiburg.informatik.ultimate.core.model.services.ILogger;
import de.uni_freiburg.informatik.ultimate.core.model.services.IUltimateServiceProvider;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.cfg.CfgSmtToolkit;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.cfg.IIcfgSymbolTable;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.cfg.structure.IIcfgTransition;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.smt.SmtUtils.SimplificationTechnique;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.smt.SmtUtils.XnfConversionTechnique;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.smt.predicates.IPredicate;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.smt.predicates.IPredicateUnifier;
import de.uni_freiburg.informatik.ultimate.plugins.generator.traceabstraction.Activator;
import de.uni_freiburg.informatik.ultimate.plugins.generator.traceabstraction.PredicateFactoryForInterpolantAutomata;
import de.uni_freiburg.informatik.ultimate.plugins.generator.traceabstraction.predicates.PredicateFactory;
import de.uni_freiburg.informatik.ultimate.plugins.generator.traceabstraction.preferences.TAPreferences.InterpolantAutomatonEnhancement;

/**
 * Constructs a danger automaton for a given error trace.
 * 
 * @author Christian Schilling (schillic@informatik.uni-freiburg.de)
 * @param <LETTER>
 *            letter type in the trace/automaton
 */
public class DangerAutomatonBuilder<LETTER extends IIcfgTransition<?>> implements IErrorAutomatonBuilder<LETTER> {
	/**
	 * {@code true} iff predicates are unified.
	 */
	private static final boolean UNIFY_PREDICATES = false;

	private final NestedWordAutomaton<LETTER, IPredicate> mResult;
	private final int mLastIteration;

	/**
	 * @param services
	 *            Ultimate services.
	 * @param predicateFactory
	 *            predicate factory
	 * @param predicateUnifier
	 *            predicate unifier
	 * @param csToolkit
	 *            SMT toolkit
	 * @param simplificationTechnique
	 *            simplification technique
	 * @param xnfConversionTechnique
	 *            XNF conversion technique
	 * @param symbolTable
	 *            symbol table
	 * @param predicateFactoryForAutomaton
	 *            predicate factory for the danger automaton (will eventually be removed by a refactoring)
	 * @param abstraction
	 *            current program abstraction
	 * @param trace
	 *            error trace
	 * @param iteration
	 *            CEGAR loop iteration in which this builder was created
	 */
	@SuppressWarnings("squid:S00107")
	public DangerAutomatonBuilder(final IUltimateServiceProvider services, final PredicateFactory predicateFactory,
			final IPredicateUnifier predicateUnifier, final CfgSmtToolkit csToolkit,
			final SimplificationTechnique simplificationTechnique, final XnfConversionTechnique xnfConversionTechnique,
			final IIcfgSymbolTable symbolTable,
			final PredicateFactoryForInterpolantAutomata predicateFactoryForAutomaton,
			final INestedWordAutomaton<LETTER, IPredicate> abstraction, final NestedWord<LETTER> trace,
			final int iteration) {
		final ILogger logger = services.getLoggingService().getLogger(Activator.PLUGIN_ID);
		mLastIteration = iteration;
		final PredicateUnificationMechanism internalPredicateUnifier =
				new PredicateUnificationMechanism(predicateUnifier, UNIFY_PREDICATES);

		mResult = constructDangerAutomaton(new AutomataLibraryServices(services), logger, predicateFactory,
				internalPredicateUnifier, csToolkit, simplificationTechnique, xnfConversionTechnique, symbolTable,
				predicateFactoryForAutomaton, abstraction, trace);
	}

	@Override
	public ErrorAutomatonType getType() {
		return ErrorAutomatonType.DANGER_AUTOMATON;
	}

	@Override
	public NestedWordAutomaton<LETTER, IPredicate> getResultBeforeEnhancement() {
		return mResult;
	}

	@Override
	public INwaOutgoingLetterAndTransitionProvider<LETTER, IPredicate> getResultAfterEnhancement() {
		return mResult;
	}

	@Override
	public IPredicate getErrorPrecondition() {
		return null;
	}

	@Override
	public boolean hasAutomatonInIteration(final int iteration) {
		return mLastIteration == iteration;
	}

	@Override
	public InterpolantAutomatonEnhancement getEnhancementMode() {
		return InterpolantAutomatonEnhancement.NONE;
	}

	private NestedWordAutomaton<LETTER, IPredicate> constructDangerAutomaton(final AutomataLibraryServices services,
			final ILogger logger, final PredicateFactory predicateFactory,
			final PredicateUnificationMechanism predicateUnifier, final CfgSmtToolkit csToolkit,
			final SimplificationTechnique simplificationTechnique, final XnfConversionTechnique xnfConversionTechnique,
			final IIcfgSymbolTable symbolTable,
			final PredicateFactoryForInterpolantAutomata predicateFactoryForAutomaton,
			final INestedWordAutomaton<LETTER, IPredicate> abstraction, final NestedWord<LETTER> trace) {
		final Map<IPredicate, IPredicate> abstState2dangState = new HashMap<>();
		final Set<IPredicate> visited = new HashSet<>();
		final Deque<IPredicate> visit = new LinkedList<>();

		final NestedWordAutomaton<LETTER, IPredicate> result =
				new NestedWordAutomaton<>(services, new VpAlphabet<>(abstraction), predicateFactoryForAutomaton);

		final IPredicate trueState = predicateUnifier.getTruePredicate();
		result.addState(false, true, trueState);
		for (final IPredicate state : abstraction.getFinalStates()) {
			abstState2dangState.put(state, trueState);
			visit.add(state);
			visited.add(state);
		}

		while (!visit.isEmpty()) {
			final IPredicate state = visit.pop();
			assert visited.contains(state);
			// TODO
		}

		return result;
	}
}
