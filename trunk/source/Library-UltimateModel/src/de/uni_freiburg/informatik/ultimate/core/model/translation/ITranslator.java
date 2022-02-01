/*
 * Copyright (C) 2014-2015 Daniel Dietsch (dietsch@informatik.uni-freiburg.de)
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
package de.uni_freiburg.informatik.ultimate.core.model.translation;

import java.util.List;

import de.uni_freiburg.informatik.ultimate.core.model.translation.IProgramExecution.ProgramState;

/**
 * Object translate traces and expressions from one format to another. In ULTIMATE generator plugins may transform one
 * program model into another. A program analysis constructs results (e.g., traces or expressions) for some program
 * model, but a user wants to see the results for the initial program model (e.g., C programming language). We use
 * ITranslater objects for a backtranslation of the program transformations that were done by plugins. <br>
 * Because {@link ITranslator} is used for <b>back-translation</b>, <i>Source</i> describes the output of a tool and
 * <i>Target</i> the input of a tool.
 *
 * @author heizmann@informatik.uni-freiburg.de,
 * @author dietsch@informatik.uni-freiburg.de
 *
 * @param <STE>
 *            Source Trace Element. Type of trace elements (e.g., Statements, CodeBlocks, BoogieASTNodes) in the source
 *            program model.
 * @param <TTE>
 *            Target Trace Element. Type of trace elements (e.g., Statements, CodeBlocks, BoogieASTNodes) in the target
 *            program model.
 * @param <SE>
 *            Source Expression. Type of expression in the source program model.
 * @param <TE>
 *            Target Expression. Type of expression in the target program model.
 * @param <SVL>
 *            Source vertex label.
 * @param <TVL>
 *            Target vertex label.
 */
public interface ITranslator<STE, TTE, SE, TE, SVL, TVL> {

	/**
	 * Note: Does not need to preserve instances
	 */
	public TE translateExpression(SE expression);

	public ProgramState<TE> translateProgramState(ProgramState<SE> programState);

	public String targetExpressionToString(TE expression);

	/**
	 * Translate trace that is represented as a list of Source Trace Elements (resp. list of Target Trace Elements).
	 *
	 * Note: Should preserve instances
	 *
	 * @return
	 */
	public List<TTE> translateTrace(List<STE> trace);

	public List<String> targetTraceToString(List<TTE> trace);

	public IProgramExecution<TTE, TE> translateProgramExecution(IProgramExecution<STE, SE> programExecution);

	public IBacktranslatedCFG<TVL, TTE> translateCFG(IBacktranslatedCFG<SVL, STE> cfg);

	public Class<? extends STE> getSourceTraceElementClass();

	public Class<? extends TTE> getTargetTraceElementClass();

	public Class<SE> getSourceExpressionClass();

	public Class<TE> getTargetExpressionClass();

}
