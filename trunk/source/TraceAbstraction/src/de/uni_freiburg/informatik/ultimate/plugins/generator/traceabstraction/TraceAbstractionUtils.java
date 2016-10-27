/*
 * Copyright (C) 2016 Matthias Heizmann (heizmann@informatik.uni-freiburg.de)
 * Copyright (C) 2016 University of Freiburg
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
package de.uni_freiburg.informatik.ultimate.plugins.generator.traceabstraction;

import java.util.ArrayList;
import java.util.Collection;
import java.util.HashSet;
import java.util.Set;
import java.util.function.Function;

import de.uni_freiburg.informatik.ultimate.automata.nestedword.INestedWordAutomaton;
import de.uni_freiburg.informatik.ultimate.core.model.services.ILogger;
import de.uni_freiburg.informatik.ultimate.core.model.services.IUltimateServiceProvider;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.boogie.ModifiableGlobalVariableManager;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.hoaretriple.IHoareTripleChecker;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.hoaretriple.IncrementalHoareTripleChecker;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.smt.managedscript.ManagedScript;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.smt.predicates.IPredicate;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.smt.predicates.MonolithicHoareTripleChecker;
import de.uni_freiburg.informatik.ultimate.plugins.generator.rcfgbuilder.cfg.CodeBlock;
import de.uni_freiburg.informatik.ultimate.plugins.generator.rcfgbuilder.cfg.ProgramPoint;
import de.uni_freiburg.informatik.ultimate.plugins.generator.traceabstraction.predicates.EfficientHoareTripleChecker;
import de.uni_freiburg.informatik.ultimate.plugins.generator.traceabstraction.predicates.IMLPredicate;
import de.uni_freiburg.informatik.ultimate.plugins.generator.traceabstraction.predicates.ISLPredicate;
import de.uni_freiburg.informatik.ultimate.plugins.generator.traceabstraction.preferences.TraceAbstractionPreferenceInitializer.HoareTripleChecks;
import de.uni_freiburg.informatik.ultimate.plugins.generator.traceabstraction.singleTraceCheck.PredicateUnifier;
import de.uni_freiburg.informatik.ultimate.util.datastructures.relation.HashRelation;

/**
 * Provides static auxiliary methods for trace abstraction.
 * @author Matthias Heizmann (heizmann@informatik.uni-freiburg.de)
 *
 */
public class TraceAbstractionUtils {

	
	
	/**
	 * @param <LCS> local control state, e.g., {@link ProgramPoint} for sequential
	 * programs or a set of {@link ProgramPoint}s for parallel programs.
	 * @param <LCSP> local control state provider, e.g., {@link ISLPredicate}, or
	 * {@link IMLPredicate}
	 */
	public static <LCSP extends IPredicate, LCS> Collection<Set<IPredicate>> computePartition(
			final INestedWordAutomaton<CodeBlock, IPredicate> automaton, final ILogger logger, final Function<LCSP, LCS> lcsProvider) {
		logger.debug("Start computation of initial partition.");
		final Collection<IPredicate> states = automaton.getStates();
		final HashRelation<LCS, IPredicate> lcs2p = new HashRelation<>();
		for (final IPredicate p : states) {
			final LCSP sp = (LCSP) p;
			lcs2p.addPair(lcsProvider.apply(sp), p);
		}
		final Collection<Set<IPredicate>> partition = new ArrayList<>();
		for (final LCS pp : lcs2p.getDomain()) {
			final Set<IPredicate> statesWithSameLcs = new HashSet<>(lcs2p.getImage(pp));
			partition.add(statesWithSameLcs);
		}
		logger.debug("Finished computation of initial partition.");
		return partition;
	}
	
	
	
	public static IHoareTripleChecker constructEfficientHoareTripleChecker(final IUltimateServiceProvider services,
			final HoareTripleChecks hoareTripleChecks, final ManagedScript mgdScript,
			final ModifiableGlobalVariableManager modGlobVarManager, final PredicateUnifier predicateUnifier)
			throws AssertionError {
		final IHoareTripleChecker solverHtc;
		switch (hoareTripleChecks) {
		case MONOLITHIC:
			solverHtc = new MonolithicHoareTripleChecker(mgdScript, modGlobVarManager);
			break;
		case INCREMENTAL:
			solverHtc = new IncrementalHoareTripleChecker(mgdScript, modGlobVarManager);
			break;
		default:
			throw new AssertionError("unknown value");
		}
		return new EfficientHoareTripleChecker(solverHtc, modGlobVarManager, predicateUnifier, mgdScript);
	}
	

}
