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

import java.util.stream.Collectors;

import de.uni_freiburg.informatik.ultimate.automata.AutomataLibraryServices;
import de.uni_freiburg.informatik.ultimate.automata.AutomataOperationCanceledException;
import de.uni_freiburg.informatik.ultimate.automata.nestedword.IDoubleDeckerAutomaton;
import de.uni_freiburg.informatik.ultimate.automata.nestedword.INwaOutgoingLetterAndTransitionProvider;
import de.uni_freiburg.informatik.ultimate.automata.nestedword.operations.RemoveDeadEnds;
import de.uni_freiburg.informatik.ultimate.automata.nestedword.operations.RemoveNonLiveStates;
import de.uni_freiburg.informatik.ultimate.core.model.services.ILogger;
import de.uni_freiburg.informatik.ultimate.core.model.services.IUltimateServiceProvider;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.cfg.structure.IIcfgTransition;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.smt.predicates.IPredicate;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.smt.predicates.PredicateFactory;
import de.uni_freiburg.informatik.ultimate.plugins.generator.traceabstraction.benchmark.LineCoverageCalculator;
import de.uni_freiburg.informatik.ultimate.witnessparser.graph.WitnessEdge;
import de.uni_freiburg.informatik.ultimate.witnessparser.graph.WitnessNode;
import de.uni_freiburg.informatik.ultimate.witnessparser.yaml.ViolationSequence;
import de.uni_freiburg.informatik.ultimate.witnessparser.yaml.Witness;

public class WitnessUtils {
	public enum Property {
		NON_REACHABILITY, TERMINATION
	}

	public WitnessUtils() {
		// do not instantiate
	}

	private static <LETTER extends IIcfgTransition<?>> IDoubleDeckerAutomaton<LETTER, IPredicate> reduce(
			final INwaOutgoingLetterAndTransitionProvider<LETTER, IPredicate> automaton, final Property property,
			final AutomataLibraryServices services) throws AutomataOperationCanceledException {
		switch (property) {
		case NON_REACHABILITY:
			return new RemoveDeadEnds<>(services, automaton).getResult();
		case TERMINATION:
			return new RemoveNonLiveStates<>(services, automaton).getResult();
		default:
			throw new AssertionError();
		}
	}

	public static <LETTER extends IIcfgTransition<?>> IDoubleDeckerAutomaton<LETTER, IPredicate>
			constructGraphMLWitnessProduct(final IUltimateServiceProvider services,
					final INwaOutgoingLetterAndTransitionProvider<LETTER, IPredicate> abstraction,
					final INwaOutgoingLetterAndTransitionProvider<WitnessEdge, WitnessNode> witnessAutomaton,
					final PredicateFactory predicateFactory, final ILogger logger, final Property property)
					throws AutomataOperationCanceledException {
		final GraphMLWitnessProductAutomaton<LETTER> wpa =
				new GraphMLWitnessProductAutomaton<>(services, abstraction, witnessAutomaton, predicateFactory);
		final LineCoverageCalculator<LETTER> origCoverage = new LineCoverageCalculator<>(services, abstraction);
		final IDoubleDeckerAutomaton<LETTER, IPredicate> newAbstraction =
				reduce(wpa, property, new AutomataLibraryServices(services));
		logger.info(wpa.generateBadWitnessInformation());
		new LineCoverageCalculator<>(services, abstraction, origCoverage).reportCoverage("Witness product");
		return newAbstraction;
	}

	public static <LETTER extends IIcfgTransition<?>> IDoubleDeckerAutomaton<LETTER, IPredicate>
			constructYamlWitnessProduct(final IUltimateServiceProvider services,
					final INwaOutgoingLetterAndTransitionProvider<LETTER, IPredicate> abstraction,
					final Witness witness, final PredicateFactory predicateFactory, final ILogger logger,
					final Property property) throws AutomataOperationCanceledException {
		final var result = new YamlWitnessProductAutomaton<>(abstraction, witness, predicateFactory);
		logger.info(
				"Constructing product of automaton with %d states and violation witness of the following lengths: %s",
				abstraction.size(), witness.getEntries().stream().map(x -> ((ViolationSequence) x).getSegments().size())
						.collect(Collectors.toList()));
		return reduce(result, property, new AutomataLibraryServices(services));
	}
}
