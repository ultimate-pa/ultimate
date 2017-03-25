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

import java.util.HashSet;
import java.util.List;
import java.util.Map;

import de.uni_freiburg.informatik.ultimate.automata.tree.ITreeRun;
import de.uni_freiburg.informatik.ultimate.core.model.services.ILogger;
import de.uni_freiburg.informatik.ultimate.logic.Annotation;
import de.uni_freiburg.informatik.ultimate.logic.Script.LBool;
import de.uni_freiburg.informatik.ultimate.logic.Term;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.hornutil.HornClause;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.smt.managedscript.ManagedScript;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.smt.predicates.IPredicate;
import de.uni_freiburg.informatik.ultimate.plugins.generator.traceabstraction.singletracecheck.PredicateUnifier;

/**
 * This is the equivalent of Automizer's TraceChecker. Here we check a tree for
 * feasibility instead of a trace.
 * 
 * @author Mostafa M.A. (mostafa.amin93@gmail.com)
 * @author Alexander Nutz (nutz@informatik.uni-freiburg.de)
 *
 */
public class TreeChecker {

	private final ITreeRun<HornClause, IPredicate> mTree;
	private final ManagedScript mBackendSmtSolverScript;
	private final HCPredicate mPostCondition;
	private final HCPredicate mPreCondition;
	private final HCSSABuilder mSSABuilder;
	private final ILogger mLogger;
	private final PredicateUnifier mPredicateUnifier;

	/***
	 * Standard constructor.
	 * 
	 * @param tree
	 * @param backendSmtSolverScript
	 * @param preCondition
	 * @param postCondition
	 * @param logger
	 * @param predicateFactory
	 * @param predicateUnifier
	 */
	public TreeChecker(final ITreeRun<HornClause, IPredicate> tree, final ManagedScript backendSmtSolverScript,
			final HCPredicate preCondition, final HCPredicate postCondition, ILogger logger,
			final PredicateUnifier predicateUnifier) {
		mTree = tree;
		mBackendSmtSolverScript = backendSmtSolverScript;
		mPostCondition = postCondition;
		mPreCondition = preCondition;
		mPredicateUnifier = predicateUnifier;
		mSSABuilder = new HCSSABuilder(mTree, mPreCondition, mPostCondition, mBackendSmtSolverScript,
				mPredicateUnifier);

		mLogger = logger;
	}

	/***
	 * Rebuild the SSA with the interpolants.
	 * 
	 * @param interpolantsMap
	 *            the map of predicates to the corresponding interpolants.
	 * @return
	 */
	public Map<IPredicate, IPredicate> rebuild(final Map<IPredicate, Term> interpolantsMap) {
		return mSSABuilder.rebuildSSApredicates(interpolantsMap);
	}

	protected HCSsa getSSA() {
		return mSSABuilder.getSSA();
	}

	protected LBool checkTrace() {
		mBackendSmtSolverScript.lock(this);
		final HCSsa ssa = getSSA();
		final List<Term> nestedExp = ssa.flatten();
		HashSet<Integer> visited = new HashSet<>();
		for (final Term t : nestedExp) {
			final Annotation ann = new Annotation(":named", ssa.getName(t));
			if (!visited.contains(ssa.getCounter(t))) {
				mLogger.debug("assert: " + ssa.getName(t) + " :: " + t.toString());
				visited.add(ssa.getCounter(t));
				final Term annT = mBackendSmtSolverScript.annotate(this, t, ann);
				mBackendSmtSolverScript.assertTerm(this, annT);
			}
		}
		final LBool result = mBackendSmtSolverScript.checkSat(this);
		mBackendSmtSolverScript.unlock(this);
		return result;
	}
}