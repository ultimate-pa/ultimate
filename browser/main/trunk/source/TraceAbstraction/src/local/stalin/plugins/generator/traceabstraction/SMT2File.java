package local.stalin.plugins.generator.traceabstraction;

import java.io.PrintWriter;

import local.stalin.logic.Atom;
import local.stalin.logic.ConnectedFormula;
import local.stalin.logic.FletFormula;
import local.stalin.logic.Formula;
import local.stalin.logic.ITEFormula;
import local.stalin.logic.LetFormula;
import local.stalin.logic.NegatedFormula;
import local.stalin.logic.QuantifiedFormula;
import local.stalin.logic.SMTLibBase;
import local.stalin.logic.TermVariable;

/**
 * Copied from evrens SafetyChecker, because I can not import it.
 * 
 *
 */
public class SMT2File {
	
	static int	ctr			= 0;
	static int 	depth		= 0;

	public static boolean writeFormulaToFile(PrintWriter pw, Formula f){
		depth++;
		String tabbing = "";
		for (int i = 0; i < depth; i++){
			tabbing += ("    ");
		}
		boolean result = true;
		
		if (f instanceof Atom){
			Atom a_f = (Atom)f;
			pw.println(tabbing + a_f.toString());
		} else if (f instanceof ConnectedFormula){
			ConnectedFormula c_f = (ConnectedFormula)f;
			pw.println(tabbing + "(" + c_f.getConnectorName());
			result = writeFormulaToFile(pw, c_f.getLhs());
			result = result && writeFormulaToFile(pw, c_f.getRhs());
			pw.println(tabbing + ")");
		} else if (f instanceof FletFormula){
			FletFormula flet_f = (FletFormula)f;
			pw.println(tabbing + "(flet ($" + flet_f.getVariable().getName() + " " + flet_f.getValue() + ") ");
			result = writeFormulaToFile(pw, flet_f.getSubFormula());
			pw.println(tabbing + ")");
		} else if (f instanceof ITEFormula){
			ITEFormula ite_f = (ITEFormula)f;
			pw.println(tabbing + "(if_then_else ");
			result = writeFormulaToFile(pw, ite_f.getCondition());
			result = result && writeFormulaToFile(pw, ite_f.getTrueCase());
			result = result && writeFormulaToFile(pw, ite_f.getFalseCase());
			pw.println(tabbing + ")");
		} else if (f instanceof LetFormula){
			LetFormula let_f = (LetFormula)f;
			pw.println(tabbing + "(let ($" + let_f.getVariable().getName() + " " + let_f.getValue() + ") ");
			result = writeFormulaToFile(pw, let_f.getSubFormula());
			pw.println(tabbing + ")");
			pw.println(tabbing + ")");
		} else if (f instanceof NegatedFormula){
			NegatedFormula not_f = (NegatedFormula)f;
			pw.println(tabbing + "(not ");
			result = writeFormulaToFile(pw, not_f.getSubFormula());
			pw.println(tabbing + ")");
		} else if (f instanceof QuantifiedFormula){
			QuantifiedFormula quant_f = (QuantifiedFormula)f;
			String quantifier = "(forall ";
			if (quant_f.getQuantifier() == QuantifiedFormula.EXISTS){
				quantifier = "(exists ";	
			}
			pw.print(tabbing + quantifier);
			for(TermVariable tv: quant_f.getVariables()){
				pw.print(tv.toString());
			}
			pw.println(" ");
			result = writeFormulaToFile(pw, quant_f.getSubformula());
			SMTLibBase[][] triggers = quant_f.getTriggers();
			if (triggers != null) {
				for (SMTLibBase[] trig : triggers) {
					pw.print(tabbing + " :pat { ");
					for (SMTLibBase term : trig) {
						pw.print(term.toString() + " ");
					}
					pw.println("}");
				}
			} else {
				pw.println(":notes This quantifier has no triggers!");
			}
			pw.println(tabbing + ")");
		} else {
			result = false;
		}
		depth--;
		return result;
	}
}
