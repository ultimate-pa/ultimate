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
import java.util.Map;

import de.uni_freiburg.informatik.ultimate.automata.tree.TreeRun;
import de.uni_freiburg.informatik.ultimate.core.model.services.ILogger;
import de.uni_freiburg.informatik.ultimate.lib.chc.HcSymbolTable;
import de.uni_freiburg.informatik.ultimate.lib.chc.HornClause;
import de.uni_freiburg.informatik.ultimate.logic.Annotation;
import de.uni_freiburg.informatik.ultimate.logic.Script.LBool;
import de.uni_freiburg.informatik.ultimate.logic.Term;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.smt.managedscript.ManagedScript;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.smt.predicates.IPredicate;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.smt.predicates.PredicateUnifier;

/**
 * This is the equivalent of Automizer's traceCheck. Here we check a tree for
 * feasibility instead of a trace.
 * 
 * @author Mostafa M.A. (mostafa.amin93@gmail.com)
 * @author Alexander Nutz (nutz@informatik.uni-freiburg.de)
 *
 */
public class TreeChecker {

	private final TreeRun<HornClause, IPredicate> mTree;
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
	 * @param symbolTable 
	 */
	public TreeChecker(final TreeRun<HornClause, IPredicate> tree, final ManagedScript backendSmtSolverScript,
			final HCPredicate preCondition, final HCPredicate postCondition, ILogger logger,
			final PredicateUnifier predicateUnifier, HcSymbolTable symbolTable) {
		mTree = tree;
		mBackendSmtSolverScript = backendSmtSolverScript;
		mPostCondition = postCondition;
		mPreCondition = preCondition;
		mPredicateUnifier = predicateUnifier;
		mSSABuilder = new HCSSABuilder(mTree, mPreCondition, mPostCondition, mBackendSmtSolverScript,
				mPredicateUnifier, symbolTable);

		mLogger = logger;
	}
	
	public TreeRun<HornClause, IPredicate> annotateTreeRunWithInterpolants(
			final Map<TreeRun<HornClause, IPredicate>, Term> interpolantsMap) {
		return mSSABuilder.buildTreeRunWithBackVersionedInterpolants(interpolantsMap);
	}

	protected HcSsaTreeFlattener getSSA() {
		return mSSABuilder.getSSA();
	}

	protected LBool checkTrace(Object lockOwner) {
		
		final HcSsaTreeFlattener ssa = getSSA();
		final Term[] nestedExp = ssa.getFlattenedTermList();
		HashSet<String> visited = new HashSet<>();
		for (final Term t : nestedExp) {
			final Annotation ann = new Annotation(":named", ssa.getName(t));
			if (!visited.contains(ssa.getName(t))) {
				mLogger.debug("assert: " + ssa.getName(t) + " :: " + t.toString());
				visited.add(ssa.getName(t));
				final Term annT = mBackendSmtSolverScript.annotate(lockOwner, t, ann);
				mBackendSmtSolverScript.assertTerm(lockOwner, annT);
			}
		}
		final LBool result = mBackendSmtSolverScript.checkSat(lockOwner);
		
		return result;
	}
}