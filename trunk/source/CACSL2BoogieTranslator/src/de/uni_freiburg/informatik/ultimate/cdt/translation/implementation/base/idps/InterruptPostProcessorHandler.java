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
import de.uni_freiburg.informatik.ultimate.core.model.models.ILocation;
import de.uni_freiburg.informatik.ultimate.core.model.services.ILogger;

public class InterruptPostProcessorHandler {
	private static final InterruptTranslationMode TRANSLATION_MODE = InterruptTranslationMode.REALIZATION_1;

	private final InterruptDrivenToThreadBasedProcessor mInterruptPostProcessor;
	private final ISRInfo mIsrInfo = TestISRInfo.isrInfo1();
	private final InterruptServiceRoutines mInterruptServiceRoutines;

	public InterruptPostProcessorHandler(final ILogger logger, final FlatSymbolTable symbolTable,
			final TranslationSettings settings, final ProcedureManager procedureManager, final CHandler chandler,
			final List<Declaration> declarations) {
		final var isrBuilder = new InterruptServiceRoutinesBuilder(declarations, mIsrInfo);
		mInterruptServiceRoutines = isrBuilder.getInterruptServiceRoutines();
		mInterruptPostProcessor = new InterruptDrivenToThreadBasedProcessor(logger, symbolTable, settings,
				procedureManager, chandler, TRANSLATION_MODE, mInterruptServiceRoutines);
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
