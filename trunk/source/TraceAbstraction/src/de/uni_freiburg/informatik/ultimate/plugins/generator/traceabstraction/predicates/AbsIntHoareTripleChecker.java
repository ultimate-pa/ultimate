/*
 * Copyright (C) 2016 Marius Greitschus (greitsch@informatik.uni-freiburg.de)
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

package de.uni_freiburg.informatik.ultimate.plugins.generator.traceabstraction.predicates;

import java.util.HashSet;
import java.util.List;
import java.util.Objects;
import java.util.Set;

import de.uni_freiburg.informatik.ultimate.boogie.BoogieVisitor;
import de.uni_freiburg.informatik.ultimate.boogie.ast.IdentifierExpression;
import de.uni_freiburg.informatik.ultimate.boogie.ast.Statement;
import de.uni_freiburg.informatik.ultimate.boogie.ast.VariableLHS;
import de.uni_freiburg.informatik.ultimate.core.model.services.ILogger;
import de.uni_freiburg.informatik.ultimate.core.model.services.IUltimateServiceProvider;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.absint.IAbstractPostOperator;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.absint.IAbstractState;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.absint.IAbstractState.SubsetResult;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.boogie.Boogie2SmtSymbolTable;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.boogie.IBoogieVar;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.cfg.structure.ICallAction;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.cfg.structure.IInternalAction;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.cfg.structure.IReturnAction;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.hoaretriple.HoareTripleCheckerStatisticsGenerator;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.hoaretriple.IHoareTripleChecker;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.smt.predicates.AbsIntPredicate;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.smt.predicates.IPredicate;
import de.uni_freiburg.informatik.ultimate.plugins.analysis.abstractinterpretationv2.algorithm.rcfg.RcfgStatementExtractor;
import de.uni_freiburg.informatik.ultimate.plugins.generator.rcfgbuilder.cfg.CodeBlock;
import de.uni_freiburg.informatik.ultimate.plugins.generator.traceabstraction.Activator;
import de.uni_freiburg.informatik.ultimate.plugins.generator.traceabstraction.singletracecheck.PredicateUnifier;
import de.uni_freiburg.informatik.ultimate.util.datastructures.relation.Pair;

/**
 * Hoare triple checker that computes predicates that are obtained from abstract interpretation in a lazy, cached
 * fashion.
 *
 * @author Marius Greitschus (greitsch@informatik.uni-freiburg.de)
 *
 */
@SuppressWarnings({ "rawtypes", "unchecked" })
public class AbsIntHoareTripleChecker<STATE extends IAbstractState<STATE, VARDECL>, ACTION, VARDECL>
		implements IHoareTripleChecker {

	private final ILogger mLogger;
	private final VariableCollector mVariableCollector;
	private final IAbstractPostOperator<STATE, ACTION, VARDECL> mPostOp;
	private final PredicateUnifier mPredicateUnifier;

	public AbsIntHoareTripleChecker(final IUltimateServiceProvider services,
			final IAbstractPostOperator<STATE, ACTION, VARDECL> postOp, final PredicateUnifier predicateUnifer) {
		mPostOp = Objects.requireNonNull(postOp);
		// TODO: Build AbsIntPredicate unifier and use it here
		mPredicateUnifier = Objects.requireNonNull(predicateUnifer);
		mLogger = services.getLoggingService().getLogger(Activator.PLUGIN_ID);
		mVariableCollector = new VariableCollector();
	}

	private Validity checkInternalTransition(final AbsIntPredicate pre, final IInternalAction act,
			final AbsIntPredicate succ) {
		assert act != null;
		assert pre != null;
		assert succ != null;
		assert false;
		if (!(act instanceof CodeBlock)) {
			throw new IllegalArgumentException("Action must be of type CodeBlock");
			// return Validity.UNKNOWN;
		}

		final IAbstractState<?, ?> preState = pre.getAbstractState();
		final IAbstractState<?, ?> postState = succ.getAbstractState();

		final CodeBlock block = (CodeBlock) act;
		final List<IAbstractState<?, ?>> postStates = applyPostInternally(preState, mPostOp, block);

		for (final IAbstractState post : postStates) {
			if (isSubsetInternally(post, postState)) {
				return Validity.VALID;
			}
		}

		return Validity.UNKNOWN;
	}

	private static List<IAbstractState<?, ?>> applyPostInternally(final IAbstractState<?, ?> currentState,
			final IAbstractPostOperator postOperator, final CodeBlock transition) {
		return postOperator.apply(currentState, transition);
	}

	private static boolean isSubsetInternally(final IAbstractState firstState, final IAbstractState secondState) {
		if (firstState.getVariables().size() != secondState.getVariables().size()) {
			return false;
		}

		if (!firstState.getVariables().stream().allMatch(secondState.getVariables()::contains)) {
			return false;
		}

		final SubsetResult subs = firstState.isSubsetOf(secondState);
		return subs != SubsetResult.NONE;
	}

	private Pair<AbsIntPredicate, AbsIntPredicate> convertPredicates(final IPredicate p1, final IPredicate p2) {
		if (!(p1 instanceof AbsIntPredicate) || !(p2 instanceof AbsIntPredicate)) {
			throw new UnsupportedOperationException(
					"The pre or post predicate is not a valid abstract state predicate.");
		}

		return new Pair<>((AbsIntPredicate) p1, (AbsIntPredicate) p2);
	}

	private static final class VariableCollector extends BoogieVisitor {
		private Set<IBoogieVar> mVariables;
		private Boogie2SmtSymbolTable mBoogie2SmtSymbolTable;

		private Set<IBoogieVar> collectVariableNames(final CodeBlock codeBlock,
				final RcfgStatementExtractor statementExtractor, final Boogie2SmtSymbolTable boogie2SmtSymbolTable) {
			mVariables = new HashSet<>();
			mBoogie2SmtSymbolTable = boogie2SmtSymbolTable;
			for (final Statement statement : statementExtractor.process(codeBlock)) {
				processStatement(statement);
			}
			return mVariables;
		}

		@Override
		protected void visit(final IdentifierExpression expr) {
			mVariables.add(
					mBoogie2SmtSymbolTable.getBoogieVar(expr.getIdentifier(), expr.getDeclarationInformation(), false));
		}

		@Override
		protected void visit(final VariableLHS lhs) {
			mVariables.add(
					mBoogie2SmtSymbolTable.getBoogieVar(lhs.getIdentifier(), lhs.getDeclarationInformation(), false));
		}
	}

	@Override
	public void releaseLock() {
		// TODO Auto-generated method stub

	}

	@Override
	public Validity checkInternal(final IPredicate pre, final IInternalAction act, final IPredicate succ) {
		// TODO Auto-generated method stub
		return null;
	}

	@Override
	public Validity checkCall(final IPredicate pre, final ICallAction act, final IPredicate succ) {
		// TODO Auto-generated method stub
		return null;
	}

	@Override
	public Validity checkReturn(final IPredicate preLin, final IPredicate preHier, final IReturnAction act,
			final IPredicate succ) {
		// TODO Auto-generated method stub
		return null;
	}

	@Override
	public HoareTripleCheckerStatisticsGenerator getEdgeCheckerBenchmark() {
		// TODO Auto-generated method stub
		return null;
	}
}
