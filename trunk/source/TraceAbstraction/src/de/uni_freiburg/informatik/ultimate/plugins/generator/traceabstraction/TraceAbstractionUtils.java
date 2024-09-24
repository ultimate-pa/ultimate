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
import de.uni_freiburg.informatik.ultimate.automata.nestedword.NestedWord;
import de.uni_freiburg.informatik.ultimate.automata.nestedword.NestedWordAutomaton;
import de.uni_freiburg.informatik.ultimate.automata.nestedword.transitions.OutgoingCallTransition;
import de.uni_freiburg.informatik.ultimate.automata.nestedword.transitions.OutgoingInternalTransition;
import de.uni_freiburg.informatik.ultimate.automata.nestedword.transitions.OutgoingReturnTransition;
import de.uni_freiburg.informatik.ultimate.automata.util.PartitionBackedSetOfPairs;
import de.uni_freiburg.informatik.ultimate.core.model.services.ILogger;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.cfg.structure.ICallAction;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.cfg.structure.IInternalAction;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.cfg.structure.IReturnAction;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.hoaretriple.HoareTripleCheckerCache;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.smt.interpolant.TracePredicates;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.smt.predicates.IMLPredicate;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.smt.predicates.IPredicate;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.smt.predicates.ISLPredicate;
import de.uni_freiburg.informatik.ultimate.lib.smtlibutils.IncrementalPlicationChecker.Validity;
import de.uni_freiburg.informatik.ultimate.plugins.generator.rcfgbuilder.cfg.BoogieIcfgLocation;
import de.uni_freiburg.informatik.ultimate.util.datastructures.relation.HashRelation;

/**
 * Provides static auxiliary methods for trace abstraction.
 *
 * @author Matthias Heizmann (heizmann@informatik.uni-freiburg.de)
 *
 */
public final class TraceAbstractionUtils {

	private TraceAbstractionUtils() {
		// do not instantiate utility class
	}

	/**
	 * @param <LCS>
	 *            local control state, e.g., {@link BoogieIcfgLocation} for sequential programs or a set of
	 *            {@link BoogieIcfgLocation}s for parallel programs.
	 * @param <LCSP>
	 *            local control state provider, e.g., {@link ISLPredicate}, or {@link IMLPredicate}
	 */
	public static <LCSP extends IPredicate, LCS> PartitionBackedSetOfPairs<IPredicate> computePartition(
			final INestedWordAutomaton<?, IPredicate> automaton, final ILogger logger,
			final Function<LCSP, LCS> lcsProvider) {
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
		return new PartitionBackedSetOfPairs<>(partition);
	}

	public static <L> String prettyPrintTracePredicates(final NestedWord<L> nestedWord,
			final TracePredicates tracePredicates) {
		if (!nestedWord.getPendingReturns().isEmpty()) {
			throw new UnsupportedOperationException();
		}
		final StringBuilder sb = new StringBuilder();
		int callStackDepth = 0;
		for (int i = 0; i < nestedWord.length(); i++) {
			sb.append("{ ");
			sb.append(tracePredicates.getPredicate(i).getFormula());
			sb.append(" }");
			sb.append(System.lineSeparator());
			if (nestedWord.isCallPosition(i)) {
				callStackDepth++;
			}
			sb.append("\t".repeat(callStackDepth));
			sb.append(nestedWord.getSymbol(i));
			sb.append(System.lineSeparator());
			if (nestedWord.isReturnPosition(i)) {
				callStackDepth--;
			}
			sb.append("\t".repeat(callStackDepth));
			// this is the postcondition for i==nestedWord.length()-1
		}
		sb.append("{ ");
		sb.append(tracePredicates.getPostcondition().getFormula());
		sb.append(" }");
		sb.append(System.lineSeparator());
		return sb.toString();
	}

	public static <L> HoareTripleCheckerCache
			extractHoareTriplesfromAutomaton(final NestedWordAutomaton<L, IPredicate> infeasibilityProof) {
		final HoareTripleCheckerCache htcc = new HoareTripleCheckerCache();
		if (infeasibilityProof == null) {
			return htcc;
		}
		for (final IPredicate state : infeasibilityProof.getStates()) {
			for (final OutgoingInternalTransition<L, IPredicate> succ : infeasibilityProof.internalSuccessors(state)) {
				htcc.putInternal(state, (IInternalAction) succ.getLetter(), succ.getSucc(), Validity.VALID);
			}

			for (final OutgoingCallTransition<L, IPredicate> succ : infeasibilityProof.callSuccessors(state)) {
				htcc.putCall(state, (ICallAction) succ.getLetter(), succ.getSucc(), Validity.VALID);
			}

			for (final OutgoingReturnTransition<L, IPredicate> succ : infeasibilityProof.returnSuccessors(state)) {
				htcc.putReturn(state, succ.getHierPred(), (IReturnAction) succ.getLetter(), succ.getSucc(),
						Validity.VALID);
			}
		}
		return htcc;
	}
}
