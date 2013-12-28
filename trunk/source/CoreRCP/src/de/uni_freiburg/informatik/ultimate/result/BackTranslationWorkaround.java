package de.uni_freiburg.informatik.ultimate.result;

import java.util.ArrayList;
import java.util.List;

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
	public static String backtranslate(
			List<ITranslator<?, ?, ?, ?>> translator_sequence,
			Expression expr) {
		List<ITranslator<?, ?, ?, ?>> translators_copy = new ArrayList<ITranslator<?, ?, ?, ?>>(translator_sequence);
		ITranslator<?, ?, ?, ?> first = translators_copy.remove(0);
		Object backExpr = first.translateExpressionIteratively(expr,
				translators_copy.toArray(new ITranslator[0]));
		
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
	
	public static String backtranslate(
			List<ITranslator<?, ?, ?, ?>> translator_sequence,
			IProgramExecution<?, ?> programExecution) {
		List<ITranslator<?, ?, ?, ?>> translators_copy = new ArrayList<ITranslator<?, ?, ?, ?>>(translator_sequence);
		ITranslator<?, ?, ?, ?> first = translators_copy.remove(0);
		Object backPE = first.translateExpressionIteratively(programExecution,
				translators_copy.toArray(new ITranslator[0]));
		return backPE.toString();
	}
	
}
