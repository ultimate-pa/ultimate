/*
 * Copyright (C) 2021 Dominik Klumpp (klumpp@informatik.uni-freiburg.de)
 * Copyright (C) 2021 University of Freiburg
 *
 * This file is part of the ULTIMATE TraceCheckerUtils Library.
 *
 * The ULTIMATE TraceCheckerUtils Library is free software: you can redistribute it and/or modify
 * it under the terms of the GNU Lesser General Public License as published
 * by the Free Software Foundation, either version 3 of the License, or
 * (at your option) any later version.
 *
 * The ULTIMATE TraceCheckerUtils Library is distributed in the hope that it will be useful,
 * but WITHOUT ANY WARRANTY; without even the implied warranty of
 * MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
 * GNU Lesser General Public License for more details.
 *
 * You should have received a copy of the GNU Lesser General Public License
 * along with the ULTIMATE TraceCheckerUtils Library. If not, see <http://www.gnu.org/licenses/>.
 *
 * Additional permission under GNU GPL version 3 section 7:
 * If you modify the ULTIMATE TraceCheckerUtils Library, or any covered work, by linking
 * or combining it with Eclipse RCP (or a modified version of Eclipse RCP),
 * containing parts covered by the terms of the Eclipse Public License, the
 * licensors of the ULTIMATE TraceCheckerUtils Library grant you additional permission
 * to convey the resulting work.
 */
package de.uni_freiburg.informatik.ultimate.lib.tracecheckerutils.partialorder.independence;

import java.util.HashMap;
import java.util.Map;
import java.util.Set;
import java.util.stream.Collectors;

import de.uni_freiburg.informatik.ultimate.automata.partialorder.independence.IIndependenceRelation;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.cfg.CfgSmtToolkit;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.cfg.structure.IAction;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.cfg.transitions.TransFormulaBuilder;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.cfg.variables.ILocalProgramVar;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.cfg.variables.ProgramVarUtils;
import de.uni_freiburg.informatik.ultimate.lib.smtlibutils.ManagedScript;
import de.uni_freiburg.informatik.ultimate.lib.tracecheckerutils.partialorder.independence.abstraction.ICopyActionFactory;

/**
 * An independence relation that always treats the given actions as though they were from separate threads. In
 * particular, it pretends that they operate over disjoint sets of local variables. (Global variables are treated as
 * shared.)
 *
 * This kind of relation is useful in the context of parameterized programs, when we are interested in the commutativity
 * of actions from the same thread template, under the assumption that the actions belong to different thread instances.
 *
 * Note: The relation creates copies of the provided letters, but does not cache these copies. Hence, it should not be
 * used above a cache layer (such that the copied actions do not appear in the cache).
 *
 * @author Dominik Klumpp (klumpp@informatik.uni-freiburg.de)
 *
 * @param <L>
 *            The type of actions
 * @param <S>
 *            The type of conditions
 */
public class DisjointLocalsIndependenceRelation<L extends IAction, S> implements IIndependenceRelation<S, L> {
	private final IIndependenceRelation<S, L> mUnderlying;
	private final ICopyActionFactory<L> mCopyFactory;
	private final ManagedScript mMgdScript;

	private final Map<ILocalProgramVar, ILocalProgramVar> mLeftSubstitution;
	private final Map<ILocalProgramVar, ILocalProgramVar> mRightSubstitution;

	public DisjointLocalsIndependenceRelation(final IIndependenceRelation<S, L> underlying,
			final ICopyActionFactory<L> copyFactory, final CfgSmtToolkit csToolkit) {
		mUnderlying = underlying;
		mCopyFactory = copyFactory;
		mMgdScript = csToolkit.getManagedScript();

		final var localVars = collectLocalVariables(csToolkit);
		mLeftSubstitution = createVariableMapping("~~left~~", localVars);
		mRightSubstitution = createVariableMapping("~~right~~", localVars);
	}

	@Override
	public boolean isSymmetric() {
		return mUnderlying.isSymmetric();
	}

	@Override
	public boolean isConditional() {
		return mUnderlying.isConditional();
	}

	@Override
	public Dependence isIndependent(final S state, final L a, final L b) {
		// instantiate two versions of the letters to ensure that they have disjoint local variables
		final var leftA = instantiate(a, mLeftSubstitution);
		final var rightB = instantiate(a, mRightSubstitution);

		return mUnderlying.isIndependent(state, leftA, rightB);
	}

	private Map<ILocalProgramVar, ILocalProgramVar> createVariableMapping(final String prefix,
			final Set<ILocalProgramVar> localVars) {
		final var result = new HashMap<ILocalProgramVar, ILocalProgramVar>();
		for (final var variable : localVars) {
			final var identifier = prefix + variable.getIdentifier();
			final var copy = ProgramVarUtils.constructLocalProgramVar(identifier, variable.getProcedure(),
					variable.getSort(), mMgdScript, null);
			result.put(variable, copy);
		}
		return result;
	}

	private L instantiate(final L edge, final Map<ILocalProgramVar, ILocalProgramVar> mapping) {
		final var tf = edge.getTransformula();
		final var copyTf = TransFormulaBuilder.constructCopy(mMgdScript, tf, mapping);
		return mCopyFactory.copy(edge, copyTf, copyTf);
	}

	private static Set<ILocalProgramVar> collectLocalVariables(final CfgSmtToolkit csToolkit) {
		final var symbolTable = csToolkit.getSymbolTable();
		return csToolkit.getProcedures().stream().flatMap(p -> symbolTable.getLocals(p).stream())
				.collect(Collectors.toSet());
	}
}
