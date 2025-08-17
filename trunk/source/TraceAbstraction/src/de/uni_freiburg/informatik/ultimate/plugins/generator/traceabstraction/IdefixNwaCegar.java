package de.uni_freiburg.informatik.ultimate.plugins.generator.traceabstraction;

import java.util.Set;

import de.uni_freiburg.informatik.ultimate.automata.nestedword.INestedWordAutomaton;
import de.uni_freiburg.informatik.ultimate.core.model.services.IUltimateServiceProvider;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.cfg.CfgSmtToolkit;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.cfg.structure.IIcfg;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.cfg.structure.debugidentifiers.DebugIdentifier;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.smt.predicates.PredicateFactory;
import de.uni_freiburg.informatik.ultimate.lib.proofs.floydhoare.NwaHoareProofProducer;
import de.uni_freiburg.informatik.ultimate.plugins.generator.traceabstraction.preferences.TAPreferences;

public class IdefixNwaCegar extends NwaCegarLoop {

	/**
	 * CEGAR loop for Idefix, it creates a error automaton that accepts all feasible path upon termination
	 *
	 * Union of error autoamta minimization of error automata
	 *
	 * Dont stop after first violation
	 *
	 * Important violation witness containing the minimized union
	 *
	 * @param name
	 * @param initialAbstraction
	 * @param rootNode
	 * @param csToolkit
	 * @param predicateFactory
	 * @param taPrefs
	 * @param errorLocs
	 * @param proofProducer
	 * @param services
	 * @param transitionClazz
	 * @param stateFactoryForRefinement
	 */
	public IdefixNwaCegar(final DebugIdentifier name, final INestedWordAutomaton initialAbstraction,
			final IIcfg rootNode, final CfgSmtToolkit csToolkit, final PredicateFactory predicateFactory,
			final TAPreferences taPrefs, final Set errorLocs, final NwaHoareProofProducer proofProducer,
			final IUltimateServiceProvider services, final Class transitionClazz,
			final PredicateFactoryRefinement stateFactoryForRefinement) {
		super(name, initialAbstraction, rootNode, csToolkit, predicateFactory, taPrefs, errorLocs, proofProducer,
				services, transitionClazz, stateFactoryForRefinement);
		// TODO Auto-generated constructor stub
	}

}
