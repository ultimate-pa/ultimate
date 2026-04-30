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
import java.util.Map;

import org.eclipse.cdt.core.dom.ast.IASTNode;

import de.uni_freiburg.informatik.ultimate.boogie.ast.Declaration;
import de.uni_freiburg.informatik.ultimate.boogie.ast.Statement;
import de.uni_freiburg.informatik.ultimate.cdt.translation.implementation.FlatSymbolTable;
import de.uni_freiburg.informatik.ultimate.cdt.translation.implementation.base.CHandler;
import de.uni_freiburg.informatik.ultimate.cdt.translation.implementation.base.TranslationSettings;
import de.uni_freiburg.informatik.ultimate.cdt.translation.implementation.base.chandler.InterruptPostProcessor;
import de.uni_freiburg.informatik.ultimate.cdt.translation.implementation.base.chandler.ProcedureManager;
import de.uni_freiburg.informatik.ultimate.cdt.translation.implementation.base.expressiontranslation.ExpressionTranslation;
import de.uni_freiburg.informatik.ultimate.cdt.translation.implementation.container.AuxVarInfoBuilder;
import de.uni_freiburg.informatik.ultimate.core.model.models.ILocation;
import de.uni_freiburg.informatik.ultimate.core.model.services.ILogger;

public class InterruptPostProcessorHandler {
	private final InterruptPostProcessor mInterruptPostProcessor;
	private final ISRInfo mIsrInfo;
	private final InterruptServiceRoutines mInterruptServiceRoutines;

	private final InterruptTranslationMode mTranslationMode;

	public InterruptPostProcessorHandler(final ILogger logger, final FlatSymbolTable symbolTable,
			final TranslationSettings settings, final ProcedureManager procedureManager, final CHandler chandler,
			final AuxVarInfoBuilder auxVarInfoBuilder, final ExpressionTranslation expressionTranslation,
			final List<Declaration> declarations) {
		mTranslationMode = settings.interruptTranslationMode();
		mIsrInfo = getIsrInfo(settings);
		final var isrBuilder = new InterruptServiceRoutinesBuilder(declarations, mIsrInfo, logger);
		mInterruptServiceRoutines = isrBuilder.getInterruptServiceRoutines();
		mInterruptPostProcessor = new InterruptPostProcessor(logger, symbolTable, settings, procedureManager, chandler,
				auxVarInfoBuilder, expressionTranslation, mInterruptServiceRoutines);
	}

	public List<Declaration> postProcess(final ILocation loc, final IASTNode hook,
			final List<Statement> additionalInitializations) {
		if (mTranslationMode == InterruptTranslationMode.NONE) {
			return List.of();
		}
		return mInterruptPostProcessor.postProcess(loc, hook, additionalInitializations);
	}

	public List<Statement> getAdditionalInitializations() {
		return mInterruptPostProcessor.getAdditionalInitializations();
	}

	private ISRInfo getIsrInfo(final TranslationSettings settings) {
		final var currentInfo = settings.currentIsrInfo();
		if (currentInfo == CurrentIsrInfo.INFO_1) {
			return TestISRInfo.isrInfo1();
		} else if (currentInfo == CurrentIsrInfo.INFO_2) {
			return TestISRInfo.isrInfo2();
		} else if (currentInfo == CurrentIsrInfo.INFO_10) {
			return TestISRInfo.isrInfo10();
		} else if (currentInfo == CurrentIsrInfo.INFO_1_DISABLE) {
			return TestISRInfo.isrInfo1Disable();
		} else {
			return TestISRInfo.isrInfoLarge();
		}
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

		public static ISRInfo isrInfo1Disable() {
			final var isr = "isr_gpio";
			final var numToISR = new HashMap<Integer, String>();
			numToISR.put(1, isr);
			final var reqEnable = "HAL_GPIO_Enable_Int";
			final var numToReqEnable = new HashMap<Integer, String>();
			numToReqEnable.put(1, reqEnable);
			final var reqDisable = "HAL_GPIO_Disable_Int";
			final var numToReqDisable = new HashMap<Integer, String>();
			numToReqDisable.put(1, reqDisable);
			return new ISRInfo(numToISR, numToReqEnable, numToReqDisable, null, null);
		}

		public static ISRInfo isrInfo2() {
			final var isr1 = "isr1_gpio";
			final var isr2 = "isr2_gpio";
			final var numToISR = new HashMap<Integer, String>();
			numToISR.put(1, isr1);
			numToISR.put(2, isr2);
			final var reqEnable1 = "HAL_GPIO_Enable_Int1";
			final var reqEnable2 = "HAL_GPIO_Enable_Int2";
			final var numToReqEnable = new HashMap<Integer, String>();
			numToReqEnable.put(1, reqEnable1);
			numToReqEnable.put(2, reqEnable2);
			return new ISRInfo(numToISR, numToReqEnable, null, null, null);
		}

		public static ISRInfo isrInfo10() {
			final Map<Integer, String> numToISR = new HashMap<>();
			final Map<Integer, String> numToReqEnable = new HashMap<>();

			for (int i = 1; i <= 10; i++) {
				final String isrName = "isr" + i + "_gpio";
				final String reqEnableName = "HAL_GPIO_Enable_Int" + i;

				numToISR.put(i, isrName);
				numToReqEnable.put(i, reqEnableName);
			}
			return new ISRInfo(numToISR, numToReqEnable, null, null, null);
		}

		public static ISRInfo isrInfoLarge() {
			final var isr = "HAL_GPIO_EXTI_Callback";
			final var numToISR = new HashMap<Integer, String>();
			numToISR.put(1, isr);
			final var reqEnable = "MX_GPIO_Init";
			final var numToReqEnable = new HashMap<Integer, String>();
			numToReqEnable.put(1, reqEnable);
			final var reqDisable = "HAL_GPIO_DeInit";
			final var numToReqDisable = new HashMap<Integer, String>();
			numToReqDisable.put(1, reqDisable);
			return new ISRInfo(numToISR, numToReqEnable, numToReqDisable, null, null);
		}
	}
}
