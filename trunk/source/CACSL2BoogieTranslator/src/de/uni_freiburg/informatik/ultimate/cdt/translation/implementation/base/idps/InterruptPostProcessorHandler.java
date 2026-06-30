/*
 * Copyright (C) 2026 Matthias Zumkeller
 * Copyright (C) 2026 University of Freiburg
 *
 * This file is part of the ULTIMATE CACSL2BoogieTranslator plug-in.
 *
 * The ULTIMATE CACSL2BoogieTranslator plug-in is free software: you can redistribute it and/or modify
 * it under the terms of the GNU Lesser General Public License as published
 * by the Free Software Foundation, either version 3 of the License, or
 * (at your option) any later version.
 *
 * The ULTIMATE CACSL2BoogieTranslator plug-in is distributed in the hope that it will be useful,
 * but WITHOUT ANY WARRANTY; without even the implied warranty of
 * MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
 * GNU Lesser General Public License for more details.
 *
 * You should have received a copy of the GNU Lesser General Public License
 * along with the ULTIMATE CACSL2BoogieTranslator plug-in. If not, see <http://www.gnu.org/licenses/>.
 *
 * Additional permission under GNU GPL version 3 section 7:
 * If you modify the ULTIMATE CACSL2BoogieTranslator plug-in, or any covered work, by linking
 * or combining it with Eclipse RCP (or a modified version of Eclipse RCP),
 * containing parts covered by the terms of the Eclipse Public License, the
 * licensors of the ULTIMATE CACSL2BoogieTranslator plug-in grant you additional permission
 * to convey the resulting work.
 */

package de.uni_freiburg.informatik.ultimate.cdt.translation.implementation.base.idps;

import java.util.List;

import org.eclipse.cdt.core.dom.ast.IASTNode;

import de.uni_freiburg.informatik.ultimate.boogie.ast.Declaration;
import de.uni_freiburg.informatik.ultimate.boogie.ast.Statement;
import de.uni_freiburg.informatik.ultimate.cdt.translation.implementation.base.CHandler;
import de.uni_freiburg.informatik.ultimate.cdt.translation.implementation.base.TranslationSettings;
import de.uni_freiburg.informatik.ultimate.cdt.translation.implementation.base.chandler.IPostProcessor;
import de.uni_freiburg.informatik.ultimate.cdt.translation.implementation.base.chandler.InterruptPostProcessor;
import de.uni_freiburg.informatik.ultimate.cdt.translation.implementation.base.chandler.ProcedureManager;
import de.uni_freiburg.informatik.ultimate.cdt.translation.implementation.base.expressiontranslation.ExpressionTranslation;
import de.uni_freiburg.informatik.ultimate.cdt.translation.implementation.container.AuxVarInfoBuilder;
import de.uni_freiburg.informatik.ultimate.core.model.models.ILocation;
import de.uni_freiburg.informatik.ultimate.core.model.services.ILogger;

public class InterruptPostProcessorHandler implements IPostProcessor {
	private final InterruptPostProcessor mInterruptPostProcessor;
	private final ISRInfo mIsrInfo;
	private final InterruptServiceRoutines mInterruptServiceRoutines;

	private final InterruptTranslationMode mTranslationMode;

	public InterruptPostProcessorHandler(final ILogger logger, final TranslationSettings settings,
			final ProcedureManager procedureManager, final CHandler chandler, final AuxVarInfoBuilder auxVarInfoBuilder,
			final ExpressionTranslation expressionTranslation, final List<Declaration> declarations) {
		mTranslationMode = settings.interruptTranslationMode();
		mInterruptPostProcessor = new InterruptPostProcessor(logger, settings, procedureManager, chandler,
				auxVarInfoBuilder, expressionTranslation, mInterruptServiceRoutines);
	}

	public List<Statement> getAdditionalInitializations() {
		return mInterruptPostProcessor.getAdditionalInitializations();
	}

	@Override
	public List<Declaration> postProcess(ILocation loc, IASTNode hook, List<Statement> additionalInitializations) {
		if (mTranslationMode == InterruptTranslationMode.NONE) {
			return List.of();
		}
		return mInterruptPostProcessor.postProcess(loc, hook, additionalInitializations);
	}

}
