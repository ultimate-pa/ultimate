/*
 * Copyright (C) 2026 Matthias Zumkeller
 * Copyright (C) 2026 University of Freiburg
 *
 * This file is part of the ULTIMATE CACSL2BoogieTranslator plug-in.
 *
 * The ULTIMATE BoogiePreprocessor plug-in is free software: you can redistribute it and/or modify
 * it under the terms of the GNU Lesser General Public License as published
 * by the Free Software Foundation, either version 3 of the License, or
 * (at your option) any later version.
 *
 * The ULTIMATE BoogiePreprocessor plug-in is distributed in the hope that it will be useful,
 * but WITHOUT ANY WARRANTY; without even the implied warranty of
 * MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
 * GNU Lesser General Public License for more details.
 *
 * You should have received a copy of the GNU Lesser General Public License
 * along with the ULTIMATE BoogiePreprocessor plug-in. If not, see <http://www.gnu.org/licenses/>.
 *
 * Additional permission under GNU GPL version 3 section 7:
 * If you modify the ULTIMATE BoogiePreprocessor plug-in, or any covered work, by linking
 * or combining it with Eclipse RCP (or a modified version of Eclipse RCP),
 * containing parts covered by the terms of the Eclipse Public License, the
 * licensors of the ULTIMATE BoogiePreprocessor plug-in grant you additional permission
 * to convey the resulting work.
 */
package de.uni_freiburg.informatik.ultimate.cdt.translation.implementation.base.idps;

import java.util.HashMap;
import java.util.List;

import org.eclipse.cdt.core.dom.ast.IASTNode;

import de.uni_freiburg.informatik.ultimate.boogie.ast.Declaration;
import de.uni_freiburg.informatik.ultimate.boogie.ast.Statement;
import de.uni_freiburg.informatik.ultimate.cdt.translation.implementation.FlatSymbolTable;
import de.uni_freiburg.informatik.ultimate.cdt.translation.implementation.base.CHandler;
import de.uni_freiburg.informatik.ultimate.cdt.translation.implementation.base.TranslationSettings;
import de.uni_freiburg.informatik.ultimate.cdt.translation.implementation.base.chandler.InterruptDrivenToThreadBasedProcessor;
import de.uni_freiburg.informatik.ultimate.cdt.translation.implementation.base.chandler.ProcedureManager;
import de.uni_freiburg.informatik.ultimate.cdt.translation.implementation.base.expressiontranslation.ExpressionTranslation;
import de.uni_freiburg.informatik.ultimate.cdt.translation.implementation.container.AuxVarInfoBuilder;
import de.uni_freiburg.informatik.ultimate.core.model.models.ILocation;
import de.uni_freiburg.informatik.ultimate.core.model.services.ILogger;

public class InterruptPostProcessorHandler {
	private static final InterruptTranslationMode TRANSLATION_MODE = InterruptTranslationMode.REALIZATION_2;

	private final InterruptDrivenToThreadBasedProcessor mInterruptPostProcessor;
	private final ISRInfo mIsrInfo = TestISRInfo.isrInfo1();
	private final InterruptServiceRoutines mInterruptServiceRoutines;

	public InterruptPostProcessorHandler(final ILogger logger, final FlatSymbolTable symbolTable,
			final TranslationSettings settings, final ProcedureManager procedureManager, final CHandler chandler,
			final AuxVarInfoBuilder auxVarInfoBuilder, final ExpressionTranslation expressionTranslation,
			final List<Declaration> declarations) {
		final var isrBuilder = new InterruptServiceRoutinesBuilder(declarations, mIsrInfo);
		mInterruptServiceRoutines = isrBuilder.getInterruptServiceRoutines();
		mInterruptPostProcessor =
				new InterruptDrivenToThreadBasedProcessor(logger, symbolTable, settings, procedureManager, chandler,
						auxVarInfoBuilder, expressionTranslation, TRANSLATION_MODE, mInterruptServiceRoutines);
	}

	public List<Declaration> postProcess(final ILocation loc, final IASTNode hook,
			final List<Statement> additionalInitializations) {
		return mInterruptPostProcessor.postProcess(loc, hook, additionalInitializations);
	}

	public List<Statement> getAdditionalInitializations() {
		return mInterruptPostProcessor.getAdditionalInitializations();
	}

	private static class TestISRInfo {
		public static ISRInfo isrInfo1() {
			final var isr = "isr_gpio";
			final var numToISR = new HashMap<Integer, String>();
			numToISR.put(1, isr);
			final var reqEnable = "HAL_GPIO_Enable_Int";
			final var numToReqEnable = new HashMap<Integer, String>();
			numToReqEnable.put(1, reqEnable);
			return new ISRInfo(numToISR, numToReqEnable, null, null, null);
		}
	}
}
