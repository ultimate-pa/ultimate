package de.uni_freiburg.informatik.ultimate.result;

import java.util.ArrayList;
import java.util.List;

import de.uni_freiburg.informatik.ultimate.model.DefaultTranslator;
import de.uni_freiburg.informatik.ultimate.model.ITranslator;
import de.uni_freiburg.informatik.ultimate.model.boogie.ast.Expression;
import de.uni_freiburg.informatik.ultimate.model.boogie.output.BoogieStatementPrettyPrinter;


/**
 * This is a workaround until the promised day comes where He bestoweth us
 * with a proper back-translation infrastructure.
 * 
 * @author Matthias Heizmann, Jan Leike
 */
public class BackTranslationWorkaround {
	
	/**
	 * Use Ultimate's translator sequence do translate a result expression
	 * back through the toolchain.
	 * 
	 * @param expr the resulting expression
	 * @return a string corresponding to the backtranslated expression
	 */
	public static <SE> String backtranslate(
			List<ITranslator<?, ?, ?, ?>> translator_sequence,
			SE expr) {
		Object backExpr = DefaultTranslator.translateExpressionIteratively(expr, translator_sequence.toArray(new ITranslator[0]));
		
		// If the result is a Boogie expression, we use the Boogie pretty
		// printer
		String result;
		if (backExpr instanceof String) {
			result = (String) backExpr;
		} else if (backExpr instanceof Expression) {
			result = BoogieStatementPrettyPrinter.print((Expression) backExpr);
		} else {
			result = backExpr.toString();
		}
		return result;
	}
	
	public static <TE, E> String backtranslate(
			List<ITranslator<?, ?, ?, ?>> translator_sequence,
			IProgramExecution<TE, E> programExecution) {
		List<ITranslator<?, ?, ?, ?>> translators_copy = new ArrayList<ITranslator<?, ?, ?, ?>>(translator_sequence);
		ITranslator<TE, ?, E, ?> first = (ITranslator<TE, ?, E, ?>) translators_copy.remove(0);
		Object backPE = first.translateProgramExecutionIteratively(programExecution,
				translator_sequence.toArray(new ITranslator[0]));
		return backPE.toString();
	}
	
}
