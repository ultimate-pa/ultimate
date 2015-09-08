/*
 * Copyright (C) 2015 Dirk Steinmetz
 * Copyright (C) 2015 Matthias Heizmann (heizmann@informatik.uni-freiburg.de)
 * Copyright (C) 2015 University of Freiburg
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
package de.uni_freiburg.informatik.ultimate.plugins.generator.traceabstraction.pathinvariants;

import java.util.ArrayList;
import java.util.Collection;
import java.util.HashMap;
import java.util.List;
import java.util.Map;

import org.apache.log4j.Level;
import org.apache.log4j.Logger;

import de.uni_freiburg.informatik.ultimate.automata.Word;
import de.uni_freiburg.informatik.ultimate.automata.nwalibrary.NestedRun;
import de.uni_freiburg.informatik.ultimate.core.services.IToolchainStorage;
import de.uni_freiburg.informatik.ultimate.core.services.IUltimateServiceProvider;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.boogie.ModifiableGlobalVariableManager;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.boogie.TransFormula;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.smt.predicates.IPredicate;
import de.uni_freiburg.informatik.ultimate.plugins.generator.rcfgbuilder.cfg.CodeBlock;
import de.uni_freiburg.informatik.ultimate.plugins.generator.rcfgbuilder.cfg.ProgramPoint;
import de.uni_freiburg.informatik.ultimate.plugins.generator.traceabstraction.Activator;
import de.uni_freiburg.informatik.ultimate.plugins.generator.traceabstraction.pathinvariants.internal.CFGInvariantsGenerator;
import de.uni_freiburg.informatik.ultimate.plugins.generator.traceabstraction.pathinvariants.internal.ControlFlowGraph;
import de.uni_freiburg.informatik.ultimate.plugins.generator.traceabstraction.pathinvariants.internal.ControlFlowGraph.Location;
import de.uni_freiburg.informatik.ultimate.plugins.generator.traceabstraction.pathinvariants.internal.ControlFlowGraph.Transition;
import de.uni_freiburg.informatik.ultimate.plugins.generator.traceabstraction.pathinvariants.internal.IInvariantPatternProcessor;
import de.uni_freiburg.informatik.ultimate.plugins.generator.traceabstraction.pathinvariants.internal.IInvariantPatternProcessorFactory;
import de.uni_freiburg.informatik.ultimate.plugins.generator.traceabstraction.pathinvariants.internal.ILinearInequalityInvariantPatternStrategy;
import de.uni_freiburg.informatik.ultimate.plugins.generator.traceabstraction.pathinvariants.internal.LinearInequalityInvariantPatternProcessorFactory;
import de.uni_freiburg.informatik.ultimate.plugins.generator.traceabstraction.pathinvariants.internal.LocationIndependentLinearInequalityInvariantPatternStrategy;
import de.uni_freiburg.informatik.ultimate.plugins.generator.traceabstraction.predicates.ISLPredicate;
import de.uni_freiburg.informatik.ultimate.plugins.generator.traceabstraction.predicates.SmtManager;
import de.uni_freiburg.informatik.ultimate.plugins.generator.traceabstraction.singleTraceCheck.IInterpolantGenerator;
import de.uni_freiburg.informatik.ultimate.plugins.generator.traceabstraction.singleTraceCheck.PredicateUnifier;

/**
 * Represents a map of invariants to a run, that has been generated using a
 * {@link IInvariantPatternProcessor} on the run-projected CFG.
 */
public final class PathInvariantsGenerator implements IInterpolantGenerator {

	private final NestedRun<CodeBlock, IPredicate> m_Run;
	private final IPredicate m_Precondition;
	private final IPredicate m_Postcondition;
	private final IPredicate[] m_Interpolants;
	private final PredicateUnifier m_PredicateUnifier;
	private final Logger logger;

	/**
	 * Creates a default factory.
	 * 
	 * @param services
	 *            Service provider to use, for example for logging and timeouts
	 * @param storage
	 *            IToolchainstorage of the current Ultimate toolchain.
	 * @param predicateUnifier
	 *            the predicate unifier to unify final predicates with
	 * @param smtManager
	 *            the smt manager for constructing the default
	 *            {@link IInvariantPatternProcessorFactory}
	 * @return a default invariant pattern processor factory
	 */
	private static IInvariantPatternProcessorFactory<?> createDefaultFactory(
			final IUltimateServiceProvider services,
			final IToolchainStorage storage,
			final PredicateUnifier predicateUnifier, final SmtManager smtManager) {
		final ILinearInequalityInvariantPatternStrategy strategy = new LocationIndependentLinearInequalityInvariantPatternStrategy(
				1, 1, 1, 2, 5);
		return new LinearInequalityInvariantPatternProcessorFactory(services,
				storage, predicateUnifier, smtManager, strategy);
	}

	/**
	 * Generates a map of invariants to a given run, using an
	 * {@link IInvariantPatternProcessor} produced by the default
	 * {@link IInvariantPatternProcessorFactory} (with default settings).
	 * 
	 * @param services
	 *            Service provider to use, for example for logging and timeouts
	 * @param storage
	 *            IToolchainstorage of the current Ultimate toolchain.
	 * @param run
	 *            an infeasible run to project into a CFG. Must only contain
	 *            {@link ISLPredicate}s as states.
	 * @param precondition
	 *            the predicate to use for the first program point in the run
	 * @param postcondition
	 *            the predicate to use for the last program point in the run
	 * @param predicateUnifier
	 *            the predicate unifier to unify final predicates with
	 * @param smtManager
	 *            the smt manager for constructing the default
	 *            {@link IInvariantPatternProcessorFactory}
	 * @param modGlobVarManager
	 *            reserved for future use.
	 */
	public PathInvariantsGenerator(IUltimateServiceProvider services,
			IToolchainStorage storage, NestedRun<CodeBlock, IPredicate> run,
			IPredicate precondition, IPredicate postcondition,
			PredicateUnifier predicateUnifier, SmtManager smtManager,
			ModifiableGlobalVariableManager modGlobVarManager) {
		this(services, run, precondition, postcondition, predicateUnifier,
				modGlobVarManager, createDefaultFactory(services, storage, 
						predicateUnifier, smtManager));
	}

	/**
	 * Generates a map of invariants to a given run, using an
	 * {@link IInvariantPatternProcessor} produced by a given
	 * {@link IInvariantPatternProcessorFactory}.
	 * 
	 * @param services
	 *            Service provider to use, for example for logging and timeouts
	 * @param run
	 *            an infeasible run to project into a CFG. Must only contain
	 *            {@link ISLPredicate}s as states.
	 * @param precondition
	 *            the predicate to use for the first program point in the run
	 * @param postcondition
	 *            the predicate to use for the last program point in the run
	 * @param predicateUnifier
	 *            the predicate unifier to unify final predicates with
	 * @param modGlobVarManager
	 *            reserved for future use.
	 * @param invPatternProcFactory
	 *            the factory to use with {@link CFGInvariantsGenerator}.
	 */
	public PathInvariantsGenerator(final IUltimateServiceProvider services,
			final NestedRun<CodeBlock, IPredicate> run,
			final IPredicate precondition, final IPredicate postcondition,
			final PredicateUnifier predicateUnifier,
			final ModifiableGlobalVariableManager modGlobVarManager,
			final IInvariantPatternProcessorFactory<?> invPatternProcFactory) {
		super();
		m_Run = run;
		m_Precondition = precondition;
		m_Postcondition = postcondition;
		m_PredicateUnifier = predicateUnifier;

		final Logger logService = services.getLoggingService().getLogger(
				Activator.s_PLUGIN_ID);

		this.logger = logService;

		logService.log(Level.INFO,
				"Started with a run of length " + m_Run.getLength());

		// Project path to CFG
		final int len = m_Run.getLength();
		final List<Location> locations = new ArrayList<>(len);
		final Map<ProgramPoint, Location> locationsForProgramPoint = new HashMap<ProgramPoint, Location>(
				len);
		final Collection<Transition> transitions = new ArrayList<>(len - 1);

		for (int i = 0; i < len; i++) {
			final ISLPredicate pred = (ISLPredicate) m_Run
					.getStateAtPosition(i);
			final ProgramPoint programPoint = pred.getProgramPoint();

			Location location = locationsForProgramPoint.get(programPoint);
			if (location == null) {
				location = new Location(programPoint);
				locationsForProgramPoint.put(programPoint, location);
			}

			locations.add(location);

			if (i > 0) {
				if (!m_Run.getWord().isInternalPosition(i - 1)) {
					throw new UnsupportedOperationException(
							"interprocedural traces are not supported (yet)");
				}
				final TransFormula transFormula = m_Run.getSymbol(i - 1)
						.getTransitionFormula();
				transitions.add(new Transition(transFormula, locations
						.get(i - 1), location));
			}
		}

		final ControlFlowGraph cfg = new ControlFlowGraph(locations.get(0),
				locations.get(len - 1), locations, transitions);
		logService.log(Level.INFO, "[PathInvariants] Built projected CFG, "
				+ locations.size() + " states and " + transitions.size()
				+ " transitions.");

		// Generate invariants
		final CFGInvariantsGenerator generator = new CFGInvariantsGenerator(
				services, modGlobVarManager);
		final Map<ControlFlowGraph.Location, IPredicate> invariants = generator
				.generateInvariantsFromCFG(cfg, precondition, postcondition,
						invPatternProcFactory);
		logService.log(Level.INFO, "[PathInvariants] Generated invariant map.");

		// Populate resulting array
		if (invariants != null) {
			m_Interpolants = new IPredicate[len];
			for (int i = 0; i < len; i++) {
				m_Interpolants[i] = invariants.get(locations.get(i));
				logService.log(Level.INFO, "[PathInvariants] Interpolant no "
				        + i + " " + this.m_Interpolants[i].toString());
			}
			logService.log(Level.INFO, "[PathInvariants] Invariants found and "
					+ "processed.");
			logService.log(Level.INFO, "Got a Invariant map of length "
					+ m_Interpolants.length);
		} else {
			m_Interpolants = null;
			logService.log(Level.INFO, "[PathInvariants] No invariants found.");
		}
	}

	/**
	 * {@inheritDoc}
	 */
	@Override
	public Word<CodeBlock> getTrace() {
		return m_Run.getWord();
	}

	/**
	 * {@inheritDoc}
	 */
	@Override
	public IPredicate getPrecondition() {
		return m_Precondition;
	}

	/**
	 * {@inheritDoc}
	 */
	@Override
	public IPredicate getPostcondition() {
		return m_Postcondition;
	}

	/**
	 * {@inheritDoc}
	 */
	@Override
	public Map<Integer, IPredicate> getPendingContexts() {
		throw new UnsupportedOperationException("Call/Return not supported yet");
	}
	
	/**
	 * {@inheritDoc}
	 */
	@Override
	public PredicateUnifier getPredicateUnifier() {
		return m_PredicateUnifier;
	}

	/**
	 * Returns a sequence of interpolants (see definition in
	 * {@link IInterpolantGenerator}) the trace which is m_Run.getWord() with an
	 * additional property. If the ProgramPoint and position i and k coincide
	 * the the interpolants at position i and k coincide.
	 * 
	 * @return sequence of interpolants according to the run provided in the
	 *         constructor or null if no such sequence has been found; without
	 *         first interpolant (the precondition)
	 */
	@Override
	public IPredicate[] getInterpolants() {
		if (m_Interpolants == null){
			return null;
		}
		IPredicate[] interpolantMapWithOutFirstInterpolant = new IPredicate[this.m_Interpolants.length - 2];
		for (int i = 0; i < this.m_Interpolants.length - 2; i++) {
			interpolantMapWithOutFirstInterpolant[i] = this.m_Interpolants[i+1];
		}
		return interpolantMapWithOutFirstInterpolant;
	}
}
