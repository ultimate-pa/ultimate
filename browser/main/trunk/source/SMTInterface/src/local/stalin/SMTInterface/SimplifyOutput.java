package local.stalin.SMTInterface;

import java.io.PrintWriter;
import local.stalin.logic.*;

public class SimplifyOutput {
	
	private PrintWriter writer;
	
	public SimplifyOutput(PrintWriter writer) {
		this.writer = writer;
	}
	
	public static void appendTerm(StringBuilder sb, Term t) {
		if (t instanceof ApplicationTerm) {
			ApplicationTerm app = (ApplicationTerm) t;
			FunctionSymbol fsym = app.getFunction();
			if (fsym.isIntern() && fsym.getName().equals("~")) {
				sb.append("(- 0");
			
			} else {
				sb.append('(');
				sb.append(fsym.getName());
			}
			for (Term p: app.getParameters()) {
				sb.append(' ');
				appendTerm(sb, p);
			}
			sb.append(')');
		} else if (t instanceof ITETerm) {
			ITETerm ite = (ITETerm) t;
			sb.append("(ITE ");
			appendFormula(sb, ite.getCondition());
			sb.append(' ');
			appendTerm(sb, ite.getTrueCase());
			sb.append(' ');
			appendTerm(sb, ite.getFalseCase());
			sb.append(')');
		} else if (t instanceof NumeralTerm) {
			NumeralTerm number = (NumeralTerm) t;
			sb.append(number.getNumeral());
		} else if (t instanceof RationalTerm) {
			RationalTerm rat = (RationalTerm) t;
			sb.append("(/ ").append(rat.getNumerator()).append(' ');
			sb.append(rat.getDenominator()).append(')');
		} else if (t instanceof VariableTerm) {
			VariableTerm var = (VariableTerm) t;
			sb.append('?').append(var.getVariable().getName());
		} else {
			assert false;
		}
	}
	
	public static void appendFormula(StringBuilder sb, Formula f) {
		if (f instanceof Atom) {
			if (f instanceof DistinctAtom) {
				DistinctAtom atom = (DistinctAtom) f;
				sb.append("(DISTINCT");
				for (Term t: atom.getTerms()) {
					sb.append(' ');
					appendTerm(sb, t);
				}
				sb.append(')');
			} else if (f instanceof EqualsAtom) {
				EqualsAtom atom = (EqualsAtom) f;
				Term[] terms = atom.getTerms();
				int numTerms = terms.length;
				if (numTerms == 1) {
					sb.append("TRUE");
				} else if (numTerms == 2){
					sb.append("(EQ ");
					appendTerm(sb, terms[0]);
					sb.append(' ');
					appendTerm(sb, terms[1]);
					sb.append(')');
				} else {
					sb.append("(AND");
					for (int i = 0; i < numTerms-1; i++) {
						sb.append(" (EQ ");
						appendTerm(sb, terms[i]);
						sb.append(' ');
						appendTerm(sb, terms[i+1]);
						sb.append(')');
					}
					sb.append(')');
				}
			} else if (f instanceof PredicateAtom) {
				PredicateAtom atom = (PredicateAtom) f;
				sb.append('(').append(atom.getPredicate().getName());
				for (Term t: atom.getParameters()) {
					sb.append(' ');
					appendTerm(sb, t);
				}
				sb.append(")");
			} else if (f instanceof VariableAtom) {
				VariableAtom atom = (VariableAtom) f;
				sb.append('$').append(atom.getVariable().getName());
			} else if (f == Atom.TRUE) {
				sb.append("TRUE");
			} else  {
				assert (f == Atom.FALSE);
				sb.append("FALSE");
			}
		} else if (f instanceof ConnectedFormula) {
			ConnectedFormula cf = (ConnectedFormula) f;
			switch (cf.getConnector()) {
			case ConnectedFormula.AND:
				sb.append("(AND ");
				break;
			case ConnectedFormula.OR:
				sb.append("(OR ");
				break;
			case ConnectedFormula.IMPLIES:
				sb.append("(IMPLIES ");
				break;
			case ConnectedFormula.IFF:
				sb.append("(IFF ");
				break;
			case ConnectedFormula.XOR:
				sb.append("(NOT (IFF ");
				break;
			}
			if (cf.getConnector() != ConnectedFormula.IMPLIES) {
				while (cf.getRhs() instanceof ConnectedFormula
					&& ((ConnectedFormula)cf.getRhs()).getConnector() == cf.getConnector()) {
					sb.append(" ");
					appendFormula(sb, cf.getLhs());
					cf = (ConnectedFormula) cf.getRhs();
				}
			}
			appendFormula(sb, cf.getLhs());
			sb.append(' ');
			appendFormula(sb, cf.getRhs());
			sb.append(')');
			if (cf.getConnector() == ConnectedFormula.XOR)
				sb.append(')');
		} else if (f instanceof FletFormula) {
			sb.append("(LET (");
			//while (f instanceof FletFormula) 
			{
				FletFormula flet = (FletFormula) f;
				sb.append("(FORMULA $").append(flet.getVariable().getName()).append(' ');
				appendFormula(sb, flet.getValue());
				sb.append(')');
				f = flet.getSubFormula();
			}
			sb.append(") ");
			appendFormula(sb, f);
			sb.append(')');
		} else if (f instanceof ITEFormula) {
			ITEFormula ite = (ITEFormula) f;
			sb.append("(ITE ");
			appendFormula(sb, ite.getCondition());
			sb.append(' ');
			appendFormula(sb, ite.getTrueCase());
			sb.append(' ');
			appendFormula(sb, ite.getFalseCase());
			sb.append(')');
		} else if (f instanceof LetFormula) {
			sb.append("(LET (");
			//while (f instanceof LetFormula) 
			{
				LetFormula let = (LetFormula) f;
				sb.append("(TERM ?").append(let.getVariable().getName()).append(' ');
				appendTerm(sb, let.getValue());
				sb.append(')');
				f = let.getSubFormula();
			}
			sb.append(") ");
			appendFormula(sb, f);
			sb.append(')');
		} else if (f instanceof NegatedFormula) {
			NegatedFormula neg = (NegatedFormula) f;
			sb.append("(NOT ");
			appendFormula(sb, neg.getSubFormula());
			sb.append(")");
		} else if (f instanceof QuantifiedFormula) {
			QuantifiedFormula quant = (QuantifiedFormula) f;
			if (quant.getQuantifier() == QuantifiedFormula.EXISTS)
				sb.append("(EXISTS ");
			else
				sb.append("(FORALL ");
			sb.append('(');
			String sep = "";
			for (TermVariable tv : quant.getVariables()) {
				sb.append(sep).append('?').append(tv.getName()).append(" :TYPE ").append(tv.getSort());
			    sep = " ";
			}
			sb.append(')');
			SMTLibBase[][] triggers = quant.getTriggers();
			if (triggers != null && triggers.length > 0) {
				sb.append(" (PATS");
				for (int i = 0; i < triggers.length; i++) {
					sb.append(' ');
					if (triggers[i].length == 1) {
						appendTerm(sb, (Term) triggers[i][0]);
					} else {
						sb.append("(MPAT");
						for (int j = 0; j < triggers[i].length; j++) {
							sb.append(' ');
							appendTerm(sb, (Term) triggers[i][j]);
						}
						sb.append(')');
					}
				}
				sb.append(")");
			}
			
			sb.append(' ');
			appendFormula(sb, quant.getSubformula());
			sb.append(')');
		} else {
			assert false;
		}
	}	
	
	public void dumpAxiom(Formula axiom) {
		StringBuilder sb = new StringBuilder();
		sb.append("(BG_PUSH ");
		appendFormula(sb, axiom);
		sb.append(")");
		writer.println(sb.toString());
	}

	public void dumpTheory(Theory theory) {
		writer.println("(DEFTYPE Int :BUILTIN Int)");
		writer.println("(DEFTYPE Real :BUILTIN Real)");
		writer.println("(DEFTYPE $bool :BUILTIN bool)");
		for (Sort s: theory.getSorts()) {
			if (s.isIntern())
				continue;
			writer.println("(DEFTYPE "+s.getName()+")");
		}
		///writer.println("(DEFOP stalin@true stalin@bool)");
		for (PredicateSymbol psym : theory.getPredicates()) {
			if (psym.isIntern())
				continue;
			StringBuilder sb = new StringBuilder("(DEFOP ");
			sb.append(psym.getName());
			int len = psym.getParameterCount();
			for (int i = 0; i < len; i++)
				sb.append(' ').append(psym.getParameterSort(i));
			sb.append(" $bool)");
			writer.println(sb.toString());
		}
		for (FunctionSymbol fsym : theory.getFunctions()) {
			if (fsym.isIntern())
				continue;
			StringBuilder sb = new StringBuilder("(DEFOP ");
			sb.append(fsym.getName());
			int len = fsym.getParameterCount();
			for (int i = 0; i < len; i++)
				sb.append(' ').append(fsym.getParameterSort(i));
			sb.append(' ').append(fsym.getReturnSort());
			sb.append(')');
			writer.println(sb.toString());
		}
		for (Formula ax: theory.getAxioms()) {
			dumpAxiom(ax);
		}
	}

	public void checkFormula(Formula f) {
		StringBuilder sb = new StringBuilder();
		appendFormula(sb, f);
		writer.println(sb.toString());
	}
}
