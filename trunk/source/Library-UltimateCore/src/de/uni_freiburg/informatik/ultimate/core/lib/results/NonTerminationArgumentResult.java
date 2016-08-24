/*
 * Copyright (C) 2016 Matthias Heizmann (heizmann@informatik.uni-freiburg.de)
 * Copyright (C) 2016 University of Freiburg
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
package de.uni_freiburg.informatik.ultimate.core.lib.results;

import java.util.Map;
import java.util.Map.Entry;

import de.uni_freiburg.informatik.ultimate.core.model.models.IElement;
import de.uni_freiburg.informatik.ultimate.core.model.results.IResult;
import de.uni_freiburg.informatik.ultimate.core.model.services.IBacktranslationService;

/**
 * Abstract superclass for Nontermination Arguments
 * 
 * @author Matthias Heizmann (heizmann@informatik.uni-freiburg.de)
 * @param <P>
 *            program position class
 */
public abstract class NonTerminationArgumentResult<P extends IElement, E> extends AbstractResultAtElement<P> implements IResult {


	private final Class<E> mExprClazz;
	
	public NonTerminationArgumentResult(final P element, final String plugin, final IBacktranslationService translatorSequence, final Class<E> exprClass) {
		super(element, plugin, translatorSequence);
		mExprClazz = exprClass;
	}


	@Override
	public String getShortDescription() {
		return "Nontermination argument in form of an infinite " + "program execution.";
	}

	protected String printState(final Map<E, String> state) {
		final StringBuilder sb = new StringBuilder();
		sb.append("{");
		boolean first = true;
		for (final Entry<E, String> entry : state.entrySet()) {
			final String var = mTranslatorSequence.translateExpressionToString(entry.getKey(), mExprClazz);
			if (var.contains("UnsupportedOperation")) {
				continue;
			}
			if (!first) {
				sb.append(", ");
			} else {
				first = false;
			}
			// sb.append(BoogieStatementPrettyPrinter.print(entry.getKey()));
			sb.append(var);
			// sb.append(BackTranslationWorkaround.backtranslate(
			// mTranslatorSequence, entry.getKey()));
			// TODO: apply backtranslation?
			sb.append("=");
			sb.append(entry.getValue());
		}
		sb.append("}");
		return sb.toString();
	}
	
	protected String printState2(final Map<E, E> state) {
		final StringBuilder sb = new StringBuilder();
		sb.append("{");
		boolean first = true;
		for (final Entry<E, E> entry : state.entrySet()) {
			final String var = mTranslatorSequence.translateExpressionToString(entry.getKey(), mExprClazz);
			if (!first) {
				sb.append(", ");
			} else {
				first = false;
			}
			sb.append(var);
			sb.append("=");
			final String value = mTranslatorSequence.translateExpressionToString(entry.getValue(), mExprClazz);
			sb.append(value);
		}
		sb.append("}");
		return sb.toString();
	}

}
