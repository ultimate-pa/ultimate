/*
 * Copyright (C) 2016 Alexander Nutz (nutz@informatik.uni-freiburg.de)
 * Copyright (C) 2016 Mostafa M.A. (mostafa.amin93@gmail.com)
 * Copyright (C) 2016 University of Freiburg
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

import java.util.Arrays;
import java.util.Collection;
import java.util.HashSet;
import java.util.List;
import java.util.Set;
import java.util.stream.Collectors;

import de.uni_freiburg.informatik.ultimate.automata.statefactory.IIntersectionStateFactory;
import de.uni_freiburg.informatik.ultimate.automata.statefactory.IMergeStateFactory;
import de.uni_freiburg.informatik.ultimate.automata.statefactory.ISinkStateFactory;
import de.uni_freiburg.informatik.ultimate.lib.treeautomizer.HCSymbolTable;
import de.uni_freiburg.informatik.ultimate.lib.treeautomizer.HornClausePredicateSymbol;
import de.uni_freiburg.informatik.ultimate.lib.treeautomizer.HornClausePredicateSymbol.HornClauseDontCareSymbol;
import de.uni_freiburg.informatik.ultimate.logic.Term;
import de.uni_freiburg.informatik.ultimate.logic.TermVariable;
import de.uni_freiburg.informatik.ultimate.logic.Util;
import de.uni_freiburg.informatik.ultimate.logic.simplification.SimplifyDDA;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.smt.managedscript.ManagedScript;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.smt.predicates.IPredicate;

/**
 * HornClause state factory.
 * 
 * @author Mostafa M.A. (mostafa.amin93@gmail.com)
 * @author Alexander Nutz (nutz@informatik.uni-freiburg.de)
 *
 */
public class HCStateFactory implements IMergeStateFactory<IPredicate>, IIntersectionStateFactory<IPredicate>,
		ISinkStateFactory<IPredicate> {

	private final HCPredicate mSinkState;

	private final ManagedScript mBackendSmtSolverScript;
	private final SimplifyDDA mSimplifier;

	private final HCPredicateFactory mPredicateFactory;

	private int mSer;

	/***
	 * HornClause State factory constructor.
	 * 
	 * @param backendSmtSolverScript
	 * @param predicateFactory
	 * @param symbolTable
	 */
	public HCStateFactory(final ManagedScript backendSmtSolverScript, final HCPredicateFactory predicateFactory) {
		mBackendSmtSolverScript = backendSmtSolverScript;
		mSinkState = predicateFactory.getDontCarePredicate();
		mSimplifier = new SimplifyDDA(mBackendSmtSolverScript.getScript());
		mPredicateFactory = predicateFactory;
		mSer = 0;
	}

	protected int constructFreshSerialNumber() {
		return ++mSer;
	}
	
	@Override
	public IPredicate createSinkStateContent() {
		return mSinkState;
	}

	@Override
	public IPredicate intersection(final IPredicate state1, final IPredicate state2) {
		final Set<HornClausePredicateSymbol> state1PredSymbols = new HashSet<>();
		state1PredSymbols.addAll(((HCPredicate) state1).getHcPredicateSymbols());

		final Term conjoinedFormula = mSimplifier.getSimplifiedTerm(
				Util.and(mBackendSmtSolverScript.getScript(), state1.getFormula(), state2.getFormula()));

		final Set<IPredicate> ps = new HashSet<>();
		ps.add(state1);
		ps.add(state2);

		return mPredicateFactory.newPredicate(state1PredSymbols, constructFreshSerialNumber(), conjoinedFormula,
				Arrays.asList(state1.getFormula().getFreeVars()));
	}

	@Override
	public IPredicate merge(Collection<IPredicate> states) {
		/*
		 * stricly speaking, we would have to have something like
		 * "multi-location-HCPredicate" in order to treat merging several
		 * HCPredicates (with different locations) correctly. (TODO) For now we
		 * just treat everything as a generic IPredicate..
		 */

		final Set<HornClausePredicateSymbol> mergedLocations = new HashSet<>();
		Term mergedFormula = mBackendSmtSolverScript.getScript().term("false");

		List<TermVariable> varsForHcPred = null;

		for (IPredicate pred : states) {
			if (pred instanceof HCPredicate) {
				mergedLocations.addAll(((HCPredicate) pred).getHcPredicateSymbols());
				assert varsForHcPred == null || varsForHcPred.equals(((HCPredicate) pred).getSignature()) : "merging "
						+ "predicates with a different signature. Does that make sense??";
				varsForHcPred = ((HCPredicate) pred).getSignature();
			}
			mergedFormula = mSimplifier
					.getSimplifiedTerm(Util.or(mBackendSmtSolverScript.getScript(), mergedFormula, pred.getFormula()));
		}
		if (mergedLocations.isEmpty()) {
			return mPredicateFactory.newPredicate(mergedFormula);
		} else {
			return mPredicateFactory.newPredicate(mergedLocations, constructFreshSerialNumber(), mergedFormula,
					varsForHcPred);
		}
	}

	@Override
	public IPredicate createEmptyStackState() {
		return createSinkStateContent();
	}

}