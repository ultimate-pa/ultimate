/*
 * Copyright (C) 2012-2015 Daniel Dietsch (dietsch@informatik.uni-freiburg.de)
 * Copyright (C) 2012-2015 Matthias Heizmann (heizmann@informatik.uni-freiburg.de)
 * Copyright (C) 2015 University of Freiburg
 *
 * This file is part of the ULTIMATE Core.
 *
 * The ULTIMATE Core is free software: you can redistribute it and/or modify
 * it under the terms of the GNU Lesser General Public License as published
 * by the Free Software Foundation, either version 3 of the License, or
 * (at your option) any later version.
 *
 * The ULTIMATE Core is distributed in the hope that it will be useful,
 * but WITHOUT ANY WARRANTY; without even the implied warranty of
 * MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
 * GNU Lesser General Public License for more details.
 *
 * You should have received a copy of the GNU Lesser General Public License
 * along with the ULTIMATE Core. If not, see <http://www.gnu.org/licenses/>.
 *
 * Additional permission under GNU GPL version 3 section 7:
 * If you modify the ULTIMATE Core, or any covered work, by linking
 * or combining it with Eclipse RCP (or a modified version of Eclipse RCP),
 * containing parts covered by the terms of the Eclipse Public License, the
 * licensors of the ULTIMATE Core grant you additional permission
 * to convey the resulting work.
 */
package de.uni_freiburg.informatik.ultimate.core.lib.translation;

import java.util.List;

import de.uni_freiburg.informatik.ultimate.core.model.translation.IBacktranslatedCFG;
import de.uni_freiburg.informatik.ultimate.core.model.translation.IProgramExecution;
import de.uni_freiburg.informatik.ultimate.core.model.translation.IProgramExecution.ProgramState;
import de.uni_freiburg.informatik.ultimate.core.model.translation.ITranslator;

/**
 * Concatenation of two {@link ITranslator}s.
 *
 * @author Matthias Heizmann (heizmann@informatik.uni-freiburg.de)
 *
 * @param <STE>
 *            Source Trace Element. Type of trace elements (e.g., Statements,
 *            CodeBlocks, BoogieASTNodes) in the source program model.
 * @param <TTE>
 *            Target Trace Elment. Type of trace elements (e.g., Statements,
 *            CodeBlocks, BoogieASTNodes) in the target program model.
 * @param <SE>
 *            Source Expression. Type of expression in the source program model.
 * @param <TE>
 *            Target Expression. Type of expression in the target program model.
 * @param <SVL>
 *            Source vertex label. Type of the vertex label of a
 *            {@link IBacktranslatedCFG} in the source program model.
 * @param <TVL>
 *            Target vertex label. Type of the vertex label of a
 *            {@link IBacktranslatedCFG} in the target program model.
 */
public class TranslatorConcatenation<STE, ITE, TTE, SE, IE, TE, SVL, IVL, TVL>
		implements ITranslator<STE, TTE, SE, TE, SVL, TVL> {

	private final ITranslator<STE, ITE, SE, IE, SVL, IVL> mSource2IntermediateTranslator;
	private final ITranslator<ITE, TTE, IE, TE, IVL, TVL> mIntermediate2TargetTranslator;

	public TranslatorConcatenation(final ITranslator<STE, ITE, SE, IE, SVL, IVL> source2IntermediateTranslator,
			final ITranslator<ITE, TTE, IE, TE, IVL, TVL> intermediate2TargetTranslator) {
		super();
		mSource2IntermediateTranslator = source2IntermediateTranslator;
		mIntermediate2TargetTranslator = intermediate2TargetTranslator;
	}

	@Override
	public Class<STE> getSourceTraceElementClass() {
		return mSource2IntermediateTranslator.getSourceTraceElementClass();
	}

	@Override
	public Class<TTE> getTargetTraceElementClass() {
		return mIntermediate2TargetTranslator.getTargetTraceElementClass();
	}

	@Override
	public Class<SE> getSourceExpressionClass() {
		return mSource2IntermediateTranslator.getSourceExpressionClass();
	}

	@Override
	public Class<TE> getTargetExpressionClass() {
		return mIntermediate2TargetTranslator.getTargetExpressionClass();
	}

	@SuppressWarnings("unchecked")
	@Override
	public List<TTE> translateTrace(final List<STE> trace) {
		return mIntermediate2TargetTranslator.translateTrace(mSource2IntermediateTranslator.translateTrace(trace));
	}

	@Override
	public List<String> targetTraceToString(final List<TTE> trace) {
		return mIntermediate2TargetTranslator.targetTraceToString(trace);
	}

	@Override
	public TE translateExpression(final SE expression) {
		return mIntermediate2TargetTranslator
				.translateExpression(mSource2IntermediateTranslator.translateExpression(expression));
	}

	@Override
	public String targetExpressionToString(final TE expression) {
		return mIntermediate2TargetTranslator.targetExpressionToString(expression);
	}

	@Override
	public IProgramExecution<TTE, TE> translateProgramExecution(final IProgramExecution<STE, SE> programExecution) {
		return mIntermediate2TargetTranslator
				.translateProgramExecution(mSource2IntermediateTranslator.translateProgramExecution(programExecution));
	}

	@Override
	public IBacktranslatedCFG<TVL, TTE> translateCFG(final IBacktranslatedCFG<SVL, STE> cfg) {
		return mIntermediate2TargetTranslator.translateCFG(mSource2IntermediateTranslator.translateCFG(cfg));
	}

	@Override
	public String toString() {
		final StringBuilder sb = new StringBuilder();
		sb.append(getClass().getSimpleName());
		sb.append(" SE=");
		sb.append(getSourceExpressionClass().getName());
		sb.append(" TE=");
		sb.append(getTargetExpressionClass().getName());
		sb.append(" STE=");
		sb.append(getSourceTraceElementClass().getName());
		sb.append(" TTE=");
		sb.append(getTargetTraceElementClass().getName());
		return sb.toString();
	}

	@Override
	public ProgramState<TE> translateProgramState(final ProgramState<SE> oldProgramState) {
		return mIntermediate2TargetTranslator
				.translateProgramState(mSource2IntermediateTranslator.translateProgramState(oldProgramState));
	}

}
