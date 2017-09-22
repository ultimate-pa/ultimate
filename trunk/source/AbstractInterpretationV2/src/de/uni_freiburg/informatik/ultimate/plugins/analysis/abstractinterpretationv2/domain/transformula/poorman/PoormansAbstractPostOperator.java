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

import java.util.ArrayList;
import java.util.HashMap;
import java.util.HashSet;
import java.util.List;
import java.util.Map;
import java.util.Map.Entry;
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
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.boogie.IBoogieSymbolTableVariableProvider;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.boogie.MappedTerm2Expression;
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
public class PoormansAbstractPostOperator<BACKING extends IAbstractState<BACKING>>
		implements IAbstractPostOperator<PoormanAbstractState<BACKING>, IcfgEdge> {

	private final ILogger mLogger;
	private final IAbstractDomain<BACKING, IcfgEdge> mBackingDomain;
	private final Boogie2SMT mBoogie2Smt;
	private final ManagedScript mManagedScript;
	private final IUltimateServiceProvider mServices;
	private final CodeBlockFactory mCodeBlockFactory;
	private final Boogie2SmtSymbolTableTmpVars mBoogie2SmtSymbolTable;

	protected PoormansAbstractPostOperator(final IUltimateServiceProvider services, final IIcfg<?> root,
			final IAbstractDomain<BACKING, IcfgEdge> backingDomain,
			final IBoogieSymbolTableVariableProvider variableProvider) {
		mServices = services;
		mLogger = services.getLoggingService().getLogger(Activator.PLUGIN_ID);
		final BoogieIcfgContainer boogieIcfgContainer = AbsIntUtil.getBoogieIcfgContainer(root);
		mCodeBlockFactory = boogieIcfgContainer.getCodeBlockFactory();
		mBoogie2Smt = boogieIcfgContainer.getBoogie2SMT();
		assert variableProvider instanceof Boogie2SmtSymbolTableTmpVars;
		mBoogie2SmtSymbolTable = (Boogie2SmtSymbolTableTmpVars) variableProvider;

		mManagedScript = boogieIcfgContainer.getCfgSmtToolkit().getManagedScript();
		mBackingDomain = backingDomain;
	}

	@Override
	public List<PoormanAbstractState<BACKING>> apply(final PoormanAbstractState<BACKING> oldstate,
			final IcfgEdge transition) {

		final UnmodifiableTransFormula transformula = transition.getTransformula();

		// Rename inVars in abstract state
		final Map<IProgramVarOrConst, IProgramVarOrConst> renamedInVars = transformula.getInVars().entrySet().stream()
				.collect(Collectors.toMap(entry -> entry.getKey(), entry -> getFreshProgramVar(entry.getValue())));
		final PoormanAbstractState<BACKING> renamedOldState = oldstate.renameVariables(renamedInVars);
		mLogger.debug("Renamed the following variables in the current state:");
		mLogger.debug(renamedInVars.entrySet().stream()
				.map(entry -> "  " + entry.getKey().getGloballyUniqueId() + " (" + entry.getKey().hashCode() + ") --> "
						+ entry.getValue().getGloballyUniqueId() + " (" + entry.getValue().hashCode() + ")")
				.collect(Collectors.joining("\n")));

		// Add outVars and auxVars to abstract state
		final Map<IProgramVarOrConst, IProgramVarOrConst> outVarRenaming = new HashMap<>();
		final Set<IProgramVarOrConst> newOutVars = new HashSet<>();
		for (final Entry<IProgramVar, TermVariable> entry : transformula.getOutVars().entrySet()) {
			if (!renamedInVars.values().stream()
					.anyMatch(var -> var.getGloballyUniqueId().equals(entry.getValue().getName()))) {
				final IProgramVarOrConst newOutVar = getFreshProgramVar(entry.getValue());
				newOutVars.add(newOutVar);
				outVarRenaming.put(newOutVar, entry.getKey());
			} else {
				// In this case, the outVar is also an inVar. Thus, the corresponding inVar needs to be added to the
				// renaming map to be able to restore the state after the application of abstract post.
				final Entry<IProgramVarOrConst, IProgramVarOrConst> correspondingInVar = renamedInVars.entrySet()
						.stream().filter(e -> e.getValue().getGloballyUniqueId().equals(entry.getValue().getName()))
						.findFirst().orElseGet(() -> {
							throw new UnsupportedOperationException();
						});
				outVarRenaming.put(correspondingInVar.getValue(), correspondingInVar.getKey());
			}
		}

		final Set<IProgramVarOrConst> newAuxVars = new HashSet<>();
		for (final TermVariable auxVar : transformula.getAuxVars()) {
			if (!renamedInVars.values().stream().anyMatch(var -> var.getGloballyUniqueId().equals(auxVar.getName()))
					&& !newOutVars.stream().anyMatch(var -> var.getGloballyUniqueId().equals(auxVar.getName()))) {
				final IProgramVarOrConst newAuxVar = getFreshProgramVar(auxVar);
				newAuxVars.add(newAuxVar);
			}
		}

		final Set<IProgramVarOrConst> addedVariables =
				Stream.concat(newOutVars.stream(), newAuxVars.stream()).collect(Collectors.toSet());
		if (mLogger.isDebugEnabled()) {
			mLogger.debug("Adding the following variables to the abstract state: " + addedVariables);
		}

		final PoormanAbstractState<BACKING> preState = renamedOldState.addVariables(addedVariables);

		final Set<IProgramVarOrConst> tempVars = new HashSet<>();
		tempVars.addAll(renamedInVars.values());
		tempVars.addAll(newOutVars);
		tempVars.addAll(newAuxVars);
		tempVars.forEach(var -> mBoogie2SmtSymbolTable.addTemporaryVariable((IProgramVar) var));

		// Prepare Boogie expression
		final MappedTerm2Expression mappedT2e = new MappedTerm2Expression(mBoogie2Smt.getTypeSortTranslator(),
				mBoogie2Smt.getBoogie2SmtSymbolTable(), mManagedScript);

		final Set<TermVariable> renameSet = new HashSet<>();
		renameSet.addAll(transformula.getOutVars().values());
		renameSet.addAll(transformula.getInVars().values());
		renameSet.addAll(transformula.getAuxVars());

		final Expression termExpression = mappedT2e.translate(transformula.getFormula(), renameSet);
		final AssumeStatement assume = new AssumeStatement(termExpression.getLoc(), termExpression);

		mLogger.debug("Constructed assumption expression: " + termExpression);

		final CodeBlock assumeBlock =
				mCodeBlockFactory.constructStatementSequence(null, null, assume, Origin.IMPLEMENTATION);

		// Compute the abstract post
		final List<BACKING> postStates =
				mBackingDomain.getPostOperator().apply(preState.getBackingState(), assumeBlock);

		tempVars.forEach(var -> mBoogie2SmtSymbolTable.removeTemporaryVariable((IProgramVar) var));
		assert mBoogie2SmtSymbolTable.getNumberOfTempVars() == 0;

		// Remove in & aux vars from the resulting states and rename inVars back to original names.
		final Set<IProgramVarOrConst> inAuxVars = new HashSet<>();
		inAuxVars
				.addAll(renamedInVars.values().stream()
						.filter(var -> !transformula.getOutVars().values().stream()
								.anyMatch(out -> out.getName().equals(var.getGloballyUniqueId())))
						.collect(Collectors.toSet()));
		inAuxVars.addAll(newAuxVars);

		if (mLogger.isDebugEnabled()) {
			mLogger.debug("Removing the following variables from the post state: " + inAuxVars);
			mLogger.debug("Renaming the following variables: " + outVarRenaming);
		}

		final List<PoormanAbstractState<BACKING>> returnList = new ArrayList<>();
		for (final BACKING state : postStates) {
			final BACKING newState = state.removeVariables(inAuxVars).renameVariables(outVarRenaming);
			returnList.add(new PoormanAbstractState<>(mServices, mBackingDomain, newState));
		}

		return returnList;
	}

	@Override
	public List<PoormanAbstractState<BACKING>> apply(final PoormanAbstractState<BACKING> stateBeforeLeaving,
			final PoormanAbstractState<BACKING> secondState, final IcfgEdge transition) {
		// TODO Auto-generated method stub
		return null;
	}

	private IProgramVarOrConst getFreshProgramVar(final TermVariable var) {
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

			@Override
			public String toString() {
				return getGloballyUniqueId();
			}
		};
	}
}
