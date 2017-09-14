/*
 * Copyright (C) 2017 Daniel Dietsch (dietsch@informatik.uni-freiburg.de)
 * Copyright (C) 2017 Marius Greitschus (greitsch@informatik.uni-freiburg.de)
 * Copyright (C) 2017 University of Freiburg
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

package de.uni_freiburg.informatik.ultimate.plugins.analysis.abstractinterpretationv2.domain.transformula.poorman;

import java.util.HashSet;
import java.util.List;
import java.util.Map;
import java.util.Set;
import java.util.stream.Collectors;
import java.util.stream.Stream;

import de.uni_freiburg.informatik.ultimate.boogie.ast.AssumeStatement;
import de.uni_freiburg.informatik.ultimate.boogie.ast.Expression;
import de.uni_freiburg.informatik.ultimate.core.model.services.ILogger;
import de.uni_freiburg.informatik.ultimate.core.model.services.IUltimateServiceProvider;
import de.uni_freiburg.informatik.ultimate.logic.ApplicationTerm;
import de.uni_freiburg.informatik.ultimate.logic.Term;
import de.uni_freiburg.informatik.ultimate.logic.TermVariable;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.absint.IAbstractDomain;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.absint.IAbstractPostOperator;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.absint.IAbstractState;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.boogie.Boogie2SMT;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.boogie.IBoogieVar;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.boogie.MappedTerm2Expression;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.boogie.Term2Expression;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.cfg.structure.IIcfg;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.cfg.structure.IcfgEdge;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.cfg.transitions.UnmodifiableTransFormula;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.cfg.variables.IProgramVar;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.cfg.variables.IProgramVarOrConst;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.smt.managedscript.ManagedScript;
import de.uni_freiburg.informatik.ultimate.plugins.analysis.abstractinterpretationv2.Activator;
import de.uni_freiburg.informatik.ultimate.plugins.analysis.abstractinterpretationv2.util.AbsIntUtil;
import de.uni_freiburg.informatik.ultimate.plugins.generator.rcfgbuilder.cfg.BoogieIcfgContainer;
import de.uni_freiburg.informatik.ultimate.plugins.generator.rcfgbuilder.cfg.CodeBlock;
import de.uni_freiburg.informatik.ultimate.plugins.generator.rcfgbuilder.cfg.CodeBlockFactory;
import de.uni_freiburg.informatik.ultimate.plugins.generator.rcfgbuilder.cfg.StatementSequence.Origin;

/**
 *
 * @author Marius Greitschus (greitsch@informatik.uni-freiburg.de)
 *
 */
public class PoormansAbstractPostOperator<BACKING extends IAbstractState<BACKING, IBoogieVar>>
		implements IAbstractPostOperator<PoormanAbstractState<BACKING>, IcfgEdge, IProgramVarOrConst> {

	private final ILogger mLogger;
	private final IAbstractDomain<BACKING, IcfgEdge, IBoogieVar> mBackingDomain;
	private final Boogie2SMT mBoogie2Smt;
	private final ManagedScript mManagedScript;
	private final Term2Expression mTerm2Expression;
	private final IUltimateServiceProvider mServices;
	private final CodeBlockFactory mCodeBlockFactory;

	protected PoormansAbstractPostOperator(final IUltimateServiceProvider services, final IIcfg<?> root,
			final IAbstractDomain<BACKING, IcfgEdge, IBoogieVar> backingDomain) {
		mServices = services;
		mLogger = services.getLoggingService().getLogger(Activator.PLUGIN_ID);
		final BoogieIcfgContainer boogieIcfgContainer = AbsIntUtil.getBoogieIcfgContainer(root);
		mCodeBlockFactory = boogieIcfgContainer.getCodeBlockFactory();
		mBoogie2Smt = boogieIcfgContainer.getBoogie2SMT();
		mManagedScript = boogieIcfgContainer.getCfgSmtToolkit().getManagedScript();
		mBackingDomain = backingDomain;
		mTerm2Expression = mBoogie2Smt.getTerm2Expression();
	}

	@Override
	public List<PoormanAbstractState<BACKING>> apply(final PoormanAbstractState<BACKING> oldstate,
			final IcfgEdge transition) {

		final UnmodifiableTransFormula transformula = transition.getTransformula();

		if (mLogger.isDebugEnabled()) {
			mLogger.debug("Poorman abstract post apply...");
			mLogger.debug("Transformula: " + transformula);
			mLogger.debug("InVars: " + transformula.getInVars());
			mLogger.debug("OutVars: " + transformula.getOutVars());
		}

		boolean assertionsEnabled = false;
		assert assertionsEnabled = true;

		// Rename inVars in abstract state
		final Map<IProgramVarOrConst, IProgramVarOrConst> renamedInVars = transformula.getInVars().entrySet().stream()
				.collect(Collectors.toMap(entry -> entry.getKey(), entry -> getFreshProgramVar(entry.getValue())));
		final PoormanAbstractState<BACKING> renamedOldState = oldstate.renameVariables(renamedInVars);

		// Add outVars and auxVars to abstract state
		final Set<IProgramVarOrConst> newOutVars = new HashSet<>();
		for (final TermVariable outVar : transformula.getOutVars().values()) {
			if (!renamedOldState.getVariables().stream()
					.anyMatch(var -> var.getGloballyUniqueId().equals(outVar.getName()))) {
				newOutVars.add(getFreshProgramVar(outVar));
			}
		}

		final Set<IProgramVarOrConst> newAuxVars = new HashSet<>();
		for (final TermVariable auxVar : transformula.getAuxVars()) {
			if (!renamedOldState.getVariables().stream()
					.anyMatch(var -> var.getGloballyUniqueId().equals(auxVar.getName()))
					&& !newOutVars.stream().anyMatch(var -> var.getGloballyUniqueId().equals(auxVar.getName()))) {
				newAuxVars.add(getFreshProgramVar(auxVar));
			}
		}
		final PoormanAbstractState<BACKING> preState = renamedOldState
				.addVariables(Stream.concat(newOutVars.stream(), newAuxVars.stream()).collect(Collectors.toSet()));

		// Prepare Boogie expression
		final MappedTerm2Expression mappedT2e = new MappedTerm2Expression(mBoogie2Smt.getTypeSortTranslator(),
				mBoogie2Smt.getBoogie2SmtSymbolTable(), mManagedScript);

		final Set<TermVariable> renameMap = new HashSet<>();
		renameMap.addAll(transformula.getOutVars().values());

		final Expression termExpression = mappedT2e.translate(transformula.getFormula(), renameMap);
		final AssumeStatement assume = new AssumeStatement(termExpression.getLoc(), termExpression);

		final CodeBlock assumeBlock =
				mCodeBlockFactory.constructStatementSequence(null, null, assume, Origin.IMPLEMENTATION);

		mBackingDomain.getPostOperator().apply(preState.getBackingState(), assumeBlock);

		mLogger.debug("Transformula has expression: " + assume);

		if (true) {
			throw new UnsupportedOperationException("Expression: " + termExpression);
		}

		// TODO Auto-generated method stub
		return null;
	}

	@Override
	public List<PoormanAbstractState<BACKING>> apply(final PoormanAbstractState<BACKING> stateBeforeLeaving,
			final PoormanAbstractState<BACKING> secondState, final IcfgEdge transition) {
		// TODO Auto-generated method stub
		return null;
	}

	private IProgramVar getFreshProgramVar(final TermVariable var) {
		return new IProgramVar() {

			private static final long serialVersionUID = 4924620166368141045L;

			private TermVariable mTerm;

			@Override
			public String getGloballyUniqueId() {
				return var.getName();
			}

			@Override
			public boolean isGlobal() {
				return false;
			}

			@Override
			public Term getTerm() {
				return getTermVariable();
			}

			@Override
			public boolean isOldvar() {
				return false;
			}

			@Override
			public TermVariable getTermVariable() {
				if (mTerm == null) {
					mTerm = mManagedScript.variable(getGloballyUniqueId(), var.getSort());
				}
				return mTerm;
			}

			@Override
			public String getProcedure() {
				return null;
			}

			@Override
			public ApplicationTerm getPrimedConstant() {
				return null;
			}

			@Override
			public ApplicationTerm getDefaultConstant() {
				return null;
			}
		};
	}
}
