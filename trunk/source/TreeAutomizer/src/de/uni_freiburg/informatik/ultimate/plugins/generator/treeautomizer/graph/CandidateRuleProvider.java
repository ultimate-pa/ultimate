/*
 * Copyright (C) 2017 Alexander Nutz (nutz@informatik.uni-freiburg.de)
 * Copyright (C) 2017 Mostafa M.A. (mostafa.amin93@gmail.com)
 * Copyright (C) 2017 University of Freiburg
 *
 * This file is part of the ULTIMATE TreeAutomizer Plugin.
 *
 * The ULTIMATE TreeAutomizer Plugin is free software: you can redistribute it and/or modify
 * it under the terms of the GNU Lesser General Public License as published
 * by the Free Software Foundation, either version 3 of the License, or
 * (at your option) any later version.
 *
 * The ULTIMATE TreeAutomizer Plugin is distributed in the hope that it will be useful,
 * but WITHOUT ANY WARRANTY; without even the implied warranty of
 * MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
 * GNU Lesser General Public License for more details.
 *
 * You should have received a copy of the GNU Lesser General Public License
 * along with the ULTIMATE TreeAutomizer Plugin. If not, see <http://www.gnu.org/licenses/>.
 *
 * Additional permission under GNU GPL version 3 section 7:
 * If you modify the ULTIMATE TreeAutomizer Plugin, or any covered work, by linking
 * or combining it with Eclipse RCP (or a modified version of Eclipse RCP),
 * containing parts covered by the terms of the Eclipse Public License, the
 * licensors of the ULTIMATE TreeAutomizer Plugin grant you additional permission
 * to convey the resulting work.
 */
package de.uni_freiburg.informatik.ultimate.plugins.generator.treeautomizer.graph;

import java.util.HashSet;
import java.util.List;
import java.util.Set;

import de.uni_freiburg.informatik.ultimate.automata.tree.ITreeAutomatonBU;
import de.uni_freiburg.informatik.ultimate.automata.tree.TreeAutomatonRule;
import de.uni_freiburg.informatik.ultimate.lib.chc.HornClause;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.hoaretriple.IHoareTripleChecker.Validity;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.smt.predicates.IPredicate;

/**
 * Provides rules that might be added to an interpolant automaton during the generalization phase.
 *
 *
 * @author Alexander Nutz (nutz@informatik.uni-freiburg.de)
 *
 */
public class CandidateRuleProvider {



	private final Set<TreeAutomatonRule<HornClause, IPredicate>> mCandidateRules;

	/**
	 * Triggers computation of candidate rules.
	 * Result can be obtained via getter method.
	 *
	 * @param originalTreeRun
	 * @param hcSymbolsToInterpolants
	 * @param alphabet
	 */
	public CandidateRuleProvider(final ITreeAutomatonBU<HornClause, IPredicate> originalTreeRun,
			final HCHoareTripleChecker hoareTripleChecker) {
		mCandidateRules = new HashSet<>();

		for (final List<IPredicate> src : originalTreeRun.getSourceCombinations()) {
			for (final TreeAutomatonRule<HornClause, IPredicate> rule : originalTreeRun.getSuccessors(src)) {
				if (rule.getDest().equals(hoareTripleChecker.getFalsePredicate())) {
					/*
					 * Rule of the form "... -> False"
					 * Finding a new destination would be useless.
					 */
					continue;
				}
				for (final IPredicate dest : originalTreeRun.getStates()) {
					if (hoareTripleChecker.check(rule.getSource(), rule.getLetter(), dest) == Validity.VALID) {
						mCandidateRules.add(new TreeAutomatonRule<HornClause, IPredicate>(rule.getLetter(), rule.getSource(), dest));
					}
				}
			}
		}
	}

	public Iterable<TreeAutomatonRule<HornClause, IPredicate>> getCandidateRules() {
		return mCandidateRules;
	}
}
