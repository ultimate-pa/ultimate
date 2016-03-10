/*
 * Copyright (C) 2015 Daniel Dietsch (dietsch@informatik.uni-freiburg.de)
 * Copyright (C) 2015 Marius Greitschus (greitsch@informatik.uni-freiburg.de)
 * Copyright (C) 2015 University of Freiburg
 * 
 * This file is part of the ULTIMATE AbstractInterpretationV2 plug-in.
 * 
 * The ULTIMATE AbstractInterpretationV2 plug-in is free software: you can redistribute it and/or modify
 * it under the terms of the GNU Lesser General Public License as published
 * by the Free Software Foundation, either version 3 of the License, or
 * (at your option) any later version.
 * 
 * The ULTIMATE AbstractInterpretationV2 plug-in is distributed in the hope that it will be useful,
 * but WITHOUT ANY WARRANTY; without even the implied warranty of
 * MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
 * GNU Lesser General Public License for more details.
 * 
 * You should have received a copy of the GNU Lesser General Public License
 * along with the ULTIMATE AbstractInterpretationV2 plug-in. If not, see <http://www.gnu.org/licenses/>.
 * 
 * Additional permission under GNU GPL version 3 section 7:
 * If you modify the ULTIMATE AbstractInterpretationV2 plug-in, or any covered work, by linking
 * or combining it with Eclipse RCP (or a modified version of Eclipse RCP), 
 * containing parts covered by the terms of the Eclipse Public License, the 
 * licensors of the ULTIMATE AbstractInterpretationV2 plug-in grant you additional permission 
 * to convey the resulting work.
 */

package de.uni_freiburg.informatik.ultimate.plugins.analysis.abstractinterpretationv2.domain.compound;

import java.util.ArrayList;
import java.util.Iterator;
import java.util.List;

import org.apache.log4j.Logger;

import de.uni_freiburg.informatik.ultimate.boogie.type.BoogieType;
import de.uni_freiburg.informatik.ultimate.core.preferences.UltimatePreferenceStore;
import de.uni_freiburg.informatik.ultimate.logic.Script;
import de.uni_freiburg.informatik.ultimate.logic.Term;
import de.uni_freiburg.informatik.ultimate.model.boogie.IBoogieVar;
import de.uni_freiburg.informatik.ultimate.model.boogie.ast.AssumeStatement;
import de.uni_freiburg.informatik.ultimate.model.boogie.ast.BinaryExpression;
import de.uni_freiburg.informatik.ultimate.model.boogie.ast.BinaryExpression.Operator;
import de.uni_freiburg.informatik.ultimate.model.boogie.ast.Expression;
import de.uni_freiburg.informatik.ultimate.model.boogie.ast.Statement;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.boogie.Boogie2SMT;
import de.uni_freiburg.informatik.ultimate.plugins.analysis.abstractinterpretationv2.Activator;
import de.uni_freiburg.informatik.ultimate.plugins.analysis.abstractinterpretationv2.algorithm.rcfg.RcfgStatementExtractor;
import de.uni_freiburg.informatik.ultimate.plugins.analysis.abstractinterpretationv2.domain.model.IAbstractDomain;
import de.uni_freiburg.informatik.ultimate.plugins.analysis.abstractinterpretationv2.domain.model.IAbstractPostOperator;
import de.uni_freiburg.informatik.ultimate.plugins.analysis.abstractinterpretationv2.domain.model.IAbstractState;
import de.uni_freiburg.informatik.ultimate.plugins.analysis.abstractinterpretationv2.domain.model.IAbstractStateBinaryOperator;
import de.uni_freiburg.informatik.ultimate.plugins.analysis.abstractinterpretationv2.tool.AbstractInterpreter;
import de.uni_freiburg.informatik.ultimate.plugins.generator.rcfgbuilder.cfg.CodeBlock;
import de.uni_freiburg.informatik.ultimate.plugins.generator.rcfgbuilder.cfg.CodeBlockFactory;
import de.uni_freiburg.informatik.ultimate.plugins.generator.rcfgbuilder.cfg.ProgramPoint;
import de.uni_freiburg.informatik.ultimate.plugins.generator.rcfgbuilder.cfg.RootAnnot;
import de.uni_freiburg.informatik.ultimate.plugins.generator.rcfgbuilder.cfg.StatementSequence.Origin;

/**
 * Post operator of the {@link CompoundDomain}.
 * 
 * @author Marius Greitschus (greitsch@informatik.uni-freiburg.de)
 *
 */
@SuppressWarnings({ "rawtypes", "unchecked" })
public class CompoundDomainPostOperator implements IAbstractPostOperator<CompoundDomainState, CodeBlock, IBoogieVar> {

	private final Logger mLogger;
	private boolean mCreateStateAssumptions = false;
	private boolean mUseSmtSolverChecks = false;
	private final Boogie2SMT mBoogie2Smt;
	private final Script mScript;
	private final CodeBlockFactory mCodeBlockFactory;
	private final RcfgStatementExtractor mStatementExtractor;

	/**
	 * Default constructor of the {@link CompoundDomain} post operator.
	 * 
	 * @param logger
	 *            The logger.
	 * @param rootAnnotation
	 *            The {@link RootAnnot} node from the {@link AbstractInterpreter}.
	 */
	protected CompoundDomainPostOperator(Logger logger, final RootAnnot rootAnnotation) {
		mLogger = logger;
		mBoogie2Smt = rootAnnotation.getBoogie2SMT();
		mScript = rootAnnotation.getScript();
		mCodeBlockFactory = rootAnnotation.getCodeBlockFactory();
		mStatementExtractor = new RcfgStatementExtractor();

		final UltimatePreferenceStore ups = new UltimatePreferenceStore(Activator.PLUGIN_ID);
		mCreateStateAssumptions = ups.getBoolean(CompoundDomainPreferences.LABEL_CREATE_ASSUMPTIONS);
		mUseSmtSolverChecks = ups.getBoolean(CompoundDomainPreferences.LABEL_USE_SMT_SOLVER_FEASIBILITY);
	}

	@Override
	public List<CompoundDomainState> apply(CompoundDomainState oldstate, CodeBlock transition) {
		final List<CompoundDomainState> returnStates = new ArrayList<>();

		final List<IAbstractState<?, CodeBlock, IBoogieVar>> states = oldstate.getAbstractStatesList();
		final List<IAbstractDomain> domains = oldstate.getDomainList();
		assert domains.size() == states.size();

		final List<CodeBlock> transitionList = createTransitionList(transition, states);
		assert transitionList.size() == domains.size();

		final List<IAbstractState<?, CodeBlock, IBoogieVar>> resultingStates = new ArrayList<>();

		for (int i = 0; i < domains.size(); i++) {
			final List<IAbstractState> result = applyInternally(states.get(i), domains.get(i).getPostOperator(),
			        transitionList.get(i));

			if (result.size() == 0) {
				return new ArrayList<>();
			}

			IAbstractState state = result.get(0);
			for (int j = 1; j < result.size(); j++) {
				state = applyMergeInternally(state, result.get(j), domains.get(i).getMergeOperator());
			}

			if (state.isBottom()) {
				return new ArrayList<>();
			}

			resultingStates.add(state);
		}

		assert resultingStates.size() == domains.size();
		returnStates.add(new CompoundDomainState(mLogger, domains, resultingStates));

		if (mUseSmtSolverChecks) {
			// TODO implement SMT Solver checks of the state.
		}

		return returnStates;
	}

	/**
	 * Computes the transition {@link CodeBlock} for each domain. If the option is enabled that each state should be
	 * assumed before each post, a new transition {@link CodeBlock} will be created which contains an assume statement
	 * at the top corresponding to the formula representation for each state.
	 * 
	 * @param transition
	 * @param states
	 * @return
	 */
	private List<CodeBlock> createTransitionList(final CodeBlock transition,
	        final List<IAbstractState<?, CodeBlock, IBoogieVar>> states) {

		final List<CodeBlock> returnList = new ArrayList<>();

		if (mCreateStateAssumptions) {
			for (int i = 0; i < states.size(); i++) {
				returnList.add(createBlockWithoutState(states, i, transition));
			}
		} else {
			for (int i = 0; i < states.size(); i++) {
				returnList.add(transition);
			}
		}

		if (mCreateStateAssumptions && mLogger.isDebugEnabled()) {
			mLogger.debug(new StringBuilder().append("Constructed transition list for each state: ").append(returnList)
			        .toString());
		}

		return returnList;
	}

	/**
	 * Creates a new {@link CodeBlock} that includes an assume statement of all states (except the i-th state) at the
	 * top and the given {@link CodeBlock} as rest.
	 * 
	 * @param states
	 * @param index
	 * @param transition
	 * @return
	 */
	private CodeBlock createBlockWithoutState(final List<IAbstractState<?, CodeBlock, IBoogieVar>> states,
	        final int index, final CodeBlock transition) {

		final List<Expression> expressionsList = new ArrayList<>();

		for (int i = 0; i < states.size(); i++) {
			if (i == index) {
				continue;
			}

			final Term term = states.get(i).getTerm(mScript, mBoogie2Smt);
			assert term != null;
			final Expression expr = mBoogie2Smt.getTerm2Expression().translate(term);
			assert expr != null;

			expressionsList.add(expr);
		}

		assert expressionsList.size() > 0;

		Expression assumeExpression = null;
		final Iterator<Expression> iter = expressionsList.iterator();
		while (iter.hasNext()) {
			final Expression current = iter.next();

			if (assumeExpression == null) {
				assumeExpression = current;
			} else {
				assumeExpression = new BinaryExpression(current.getLocation(), BoogieType.boolType, Operator.LOGICAND,
				        assumeExpression, current);
			}

		}

		final AssumeStatement assume = new AssumeStatement(assumeExpression.getLocation(), assumeExpression);
		final List<Statement> secondStatements = new ArrayList<>();
		secondStatements.add(assume);
		secondStatements.addAll(mStatementExtractor.process(transition));
		return mCodeBlockFactory.constructStatementSequence((ProgramPoint) transition.getSource(),
		        (ProgramPoint) transition.getTarget(), secondStatements, Origin.IMPLEMENTATION);
	}

	@Override
	public List<CompoundDomainState> apply(CompoundDomainState stateBeforeLeaving,
	        CompoundDomainState stateAfterLeaving, CodeBlock transition) {
		final List<CompoundDomainState> returnStates = new ArrayList<>();

		final List<IAbstractState<?, CodeBlock, IBoogieVar>> beforeStates = stateBeforeLeaving.getAbstractStatesList();
		final List<IAbstractState<?, CodeBlock, IBoogieVar>> afterStates = stateAfterLeaving.getAbstractStatesList();
		final List<IAbstractDomain> domainsBefore = stateBeforeLeaving.getDomainList();
		final List<IAbstractDomain> domainsAfter = stateAfterLeaving.getDomainList();

		assert domainsBefore.size() == domainsAfter.size();
		assert beforeStates.size() == afterStates.size();
		assert domainsBefore.size() == beforeStates.size();

		final List<IAbstractState<?, CodeBlock, IBoogieVar>> resultingStates = new ArrayList<>();

		for (int i = 0; i < domainsBefore.size(); i++) {
			final List<IAbstractState> result = applyInternally(beforeStates.get(i), afterStates.get(i),
			        domainsBefore.get(i).getPostOperator(), transition);

			if (result.size() == 0) {
				return new ArrayList<>();
			}

			IAbstractState state = result.get(0);
			for (int j = 1; j < result.size(); j++) {
				state = applyMergeInternally(state, result.get(j), domainsBefore.get(i).getMergeOperator());
			}

			if (state.isBottom()) {
				return new ArrayList<>();
			}
			resultingStates.add(state);
		}

		assert resultingStates.size() == domainsBefore.size();
		returnStates.add(new CompoundDomainState(mLogger, domainsBefore, resultingStates));

		return returnStates;
	}

	private static List<IAbstractState> applyInternally(final IAbstractState<?, CodeBlock, IBoogieVar> currentState,
	        final IAbstractPostOperator postOperator, final CodeBlock transition) {
		return postOperator.apply(currentState, transition);
	}

	private List<IAbstractState> applyInternally(final IAbstractState<?, CodeBlock, IBoogieVar> first,
	        final IAbstractState<?, CodeBlock, IBoogieVar> second, final IAbstractPostOperator postOperator,
	        final CodeBlock transition) {
		return postOperator.apply(first, second, transition);
	}

	private static <T extends IAbstractState, M extends IAbstractStateBinaryOperator<T>> T applyMergeInternally(T first,
	        T second, M mergeOperator) {
		return mergeOperator.apply(first, second);
	}

}
