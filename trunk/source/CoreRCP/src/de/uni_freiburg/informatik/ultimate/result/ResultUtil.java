/*
 * Copyright (C) 2014-2015 Daniel Dietsch (dietsch@informatik.uni-freiburg.de)
 * Copyright (C) 2013-2015 Jan Leike (leike@informatik.uni-freiburg.de)
 * Copyright (C) 2013-2015 Matthias Heizmann (heizmann@informatik.uni-freiburg.de)
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
package de.uni_freiburg.informatik.ultimate.result;

import java.util.ArrayList;
import java.util.List;

import de.uni_freiburg.informatik.ultimate.core.services.model.IBacktranslationService;
import de.uni_freiburg.informatik.ultimate.model.DefaultTranslator;
import de.uni_freiburg.informatik.ultimate.model.IElement;
import de.uni_freiburg.informatik.ultimate.model.ITranslator;
import de.uni_freiburg.informatik.ultimate.model.annotation.IAnnotations;
import de.uni_freiburg.informatik.ultimate.model.boogie.ast.Expression;
import de.uni_freiburg.informatik.ultimate.model.boogie.output.BoogiePrettyPrinter;
import de.uni_freiburg.informatik.ultimate.model.location.ILocation;
import de.uni_freiburg.informatik.ultimate.result.model.IProgramExecution;

/**
 * 
 * @author Matthias Heizmann
 * @author Jan Leike
 */
public class ResultUtil {

	public static <TE extends IElement, E> List<ILocation> getLocationSequence(IProgramExecution<TE, E> pe) {
		List<ILocation> result = new ArrayList<ILocation>();
		for (int i = 0; i < pe.getLength(); i++) {
			AtomicTraceElement<TE> te = pe.getTraceElement(i);
			result.add(te.getTraceElement().getPayload().getLocation());
		}
		return result;
	}
	
	/**
	 * Use Ultimate's translator sequence do translate a result expression back
	 * through the toolchain.
	 * 
	 * @param expr
	 *            the resulting expression
	 * @return a string corresponding to the backtranslated expression
	 */
	public static <SE> String backtranslationWorkaround(List<ITranslator<?, ?, ?, ?>> translatorSequence, SE expr) {
		Object backExpr = DefaultTranslator.translateExpressionIteratively(expr,
				translatorSequence.toArray(new ITranslator[0]));

		// If the result is a Boogie expression, we use the Boogie pretty
		// printer
		String result;
		if (backExpr instanceof String) {
			result = (String) backExpr;
		} else if (backExpr instanceof Expression) {
			result = BoogiePrettyPrinter.print((Expression) backExpr);
		} else {
			result = backExpr.toString();
		}
		return result;
	}

	public static <SE> String translateExpressionToString(IBacktranslationService translator, Class<SE> clazz,
			SE[] expression) {
		StringBuilder sb = new StringBuilder();
		for (int i = 0; i < expression.length; ++i) {
			if (i > 0) {
				sb.append(", ");
			}
			sb.append(translator.translateExpressionToString(expression[i], clazz));
		}
		return sb.toString();
	}

	/**
	 * Return the checked specification that is checked at the error location.
	 */
	public static <ELEM extends IElement> Check getCheckedSpecification(ELEM element) {
		if (element.getPayload().hasAnnotation()) {
			IAnnotations check = element.getPayload().getAnnotations().get(Check.getIdentifier());
			return (Check) check;
		} else {
			return element.getPayload().getLocation().getOrigin().getCheck();
		}
	}
}
