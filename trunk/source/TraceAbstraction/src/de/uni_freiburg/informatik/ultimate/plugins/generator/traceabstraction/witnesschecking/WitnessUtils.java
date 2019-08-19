/*
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
package de.uni_freiburg.informatik.ultimate.plugins.generator.traceabstraction.witnesschecking;

import de.uni_freiburg.informatik.ultimate.automata.AutomataLibraryServices;
import de.uni_freiburg.informatik.ultimate.automata.AutomataOperationCanceledException;
import de.uni_freiburg.informatik.ultimate.automata.IAutomaton;
import de.uni_freiburg.informatik.ultimate.automata.nestedword.IDoubleDeckerAutomaton;
import de.uni_freiburg.informatik.ultimate.automata.nestedword.INwaOutgoingLetterAndTransitionProvider;
import de.uni_freiburg.informatik.ultimate.automata.nestedword.operations.RemoveDeadEnds;
import de.uni_freiburg.informatik.ultimate.automata.nestedword.operations.RemoveNonLiveStates;
import de.uni_freiburg.informatik.ultimate.core.model.services.ILogger;
import de.uni_freiburg.informatik.ultimate.core.model.services.IUltimateServiceProvider;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.cfg.CfgSmtToolkit;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.cfg.structure.IIcfgTransition;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.smt.predicates.IPredicate;
import de.uni_freiburg.informatik.ultimate.plugins.generator.traceabstraction.PredicateFactoryRefinement;
import de.uni_freiburg.informatik.ultimate.plugins.generator.traceabstraction.benchmark.LineCoverageCalculator;
import de.uni_freiburg.informatik.ultimate.plugins.generator.traceabstraction.predicates.PredicateFactory;
import de.uni_freiburg.informatik.ultimate.witnessparser.graph.WitnessEdge;
import de.uni_freiburg.informatik.ultimate.witnessparser.graph.WitnessNode;

public class WitnessUtils {
	
	public enum Property { NON_REACHABILITY, TERMINATION };
	

	public WitnessUtils() {
		// do not instantiate
	}
	
	public static <LETTER extends IIcfgTransition<?>>  IDoubleDeckerAutomaton<LETTER, IPredicate> constructIcfgAndWitnessProduct(
			final IUltimateServiceProvider services, final IAutomaton<LETTER, IPredicate> abstraction,
			final INwaOutgoingLetterAndTransitionProvider<WitnessEdge, WitnessNode> witnessAutomaton,
			final CfgSmtToolkit csToolkit, final PredicateFactory predicateFactory,
			final PredicateFactoryRefinement stateFactoryForRefinement, final ILogger logger, final Property property)
			throws AutomataOperationCanceledException {
		final WitnessProductAutomaton<LETTER> wpa = new WitnessProductAutomaton<LETTER>(services,
				(INwaOutgoingLetterAndTransitionProvider<LETTER, IPredicate>) abstraction, witnessAutomaton,
				csToolkit, predicateFactory, stateFactoryForRefinement);
		
		final LineCoverageCalculator<LETTER> origCoverage = new LineCoverageCalculator<>(services, abstraction);
		final IDoubleDeckerAutomaton<LETTER, IPredicate> newAbstraction;
		switch (property) {
		case NON_REACHABILITY:
			newAbstraction = new RemoveDeadEnds<>(new AutomataLibraryServices(services), wpa).getResult();
			break;
		case TERMINATION:
			newAbstraction = new RemoveNonLiveStates<>(new AutomataLibraryServices(services), wpa).getResult();
			break;
		default:
			throw new AssertionError();
		}
		logger.info(wpa.generateBadWitnessInformation());
		new LineCoverageCalculator<>(services, abstraction, origCoverage).reportCoverage("Witness product");
		return newAbstraction;
	}

}
