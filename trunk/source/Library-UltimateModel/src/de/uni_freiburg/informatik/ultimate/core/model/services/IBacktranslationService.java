/*
 * Copyright (C) 2014-2015 Daniel Dietsch (dietsch@informatik.uni-freiburg.de)
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
package de.uni_freiburg.informatik.ultimate.core.model.services;

import java.util.List;

import de.uni_freiburg.informatik.ultimate.core.model.translation.IBacktranslatedCFG;
import de.uni_freiburg.informatik.ultimate.core.model.translation.IProgramExecution;
import de.uni_freiburg.informatik.ultimate.core.model.translation.IProgramExecution.ProgramState;
import de.uni_freiburg.informatik.ultimate.core.model.translation.ITranslator;

/**
 *
 * {@link IBacktranslationService} contains all {@link ITranslator} instances for the currently running toolchain.
 *
 * @author Daniel Dietsch (dietsch@informatik.uni-freiburg.de)
 *
 */
public interface IBacktranslationService {

	/**
	 * Add a new translator to the backtranslation service. It has to be type-compatible with the existing ones!
	 *
	 * @param translator
	 */
	public <STE, TTE, SE, TE, SVL, TVL> void addTranslator(ITranslator<STE, TTE, SE, TE, SVL, TVL> translator);

	public <SE, TE> TE translateExpression(SE expression, Class<SE> sourceExpressionClass);

	/**
	 * Translate an expression from the output type to a String.
	 *
	 * @param expression
	 * @param clazz
	 * @return
	 */
	public <SE> String translateExpressionToString(SE expression, Class<SE> clazz);

	public <STE> List<?> translateTrace(List<STE> trace, Class<STE> clazz);

	public <STE> List<String> translateTraceToHumanReadableString(List<STE> trace, Class<STE> clazz);

	public <STE, SE> IProgramExecution<?, ?> translateProgramExecution(IProgramExecution<STE, SE> programExecution);
	
	public <SE> ProgramState<?> translateProgramState(ProgramState<SE> programState);

	public <STE, SE> IBacktranslatedCFG<?, ?> translateCFG(IBacktranslatedCFG<?, STE> cfg);

	/**
	 * Use this if you want to keep a certain state of the backtranslation chain during toolchain execution.
	 */
	public IBacktranslationService getTranslationServiceCopy();

}
