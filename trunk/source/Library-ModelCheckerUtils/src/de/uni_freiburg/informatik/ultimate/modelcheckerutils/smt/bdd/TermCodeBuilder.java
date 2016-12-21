package de.uni_freiburg.informatik.ultimate.modelcheckerutils.smt.bdd;

import java.math.BigDecimal;
import java.math.BigInteger;
import java.util.HashSet;
import java.util.Set;

import de.uni_freiburg.informatik.ultimate.logic.AnnotatedTerm;
import de.uni_freiburg.informatik.ultimate.logic.ApplicationTerm;
import de.uni_freiburg.informatik.ultimate.logic.ConstantTerm;
import de.uni_freiburg.informatik.ultimate.logic.FunctionSymbol;
import de.uni_freiburg.informatik.ultimate.logic.LetTerm;
import de.uni_freiburg.informatik.ultimate.logic.QuantifiedFormula;
import de.uni_freiburg.informatik.ultimate.logic.QuotedObject;
import de.uni_freiburg.informatik.ultimate.logic.Rational;
import de.uni_freiburg.informatik.ultimate.logic.Sort;
import de.uni_freiburg.informatik.ultimate.logic.Term;
import de.uni_freiburg.informatik.ultimate.logic.TermVariable;

public class TermCodeBuilder {
	
	//-------------Static-----------------
	
	public static String code(final Term term){
		return new TermCodeBuilder().buildCode(term);
	}
	
	//------------Object-------------------
	
	private final Set<Sort> sorts = new HashSet<>();
	private final Set<ConstantTerm> constants = new HashSet<>();
	private final Set<TermVariable> vars = new HashSet<>();
	private final Set<FunctionSymbol> funs = new HashSet<>();
	
	public String buildCode(final Term term){
		final StringBuilder sb = new StringBuilder();
		
		collect(term);
		
		//the sorts
		sb.append("//Sorts\n");
		for(final Sort sort : sorts){
			if(!sort.isInternal()){
				throw new UnsupportedOperationException("Sorry, I can only give you code for internal sorts");
			}
			final String s = "Sort sort_"+sort.getName()+" = script.sort(\""+sort.getName()+"\");\n";
			sb.append(s);
		}
		sb.append("\n");
		
		//the constants
		sb.append("//Constants\n");
		for(final ConstantTerm constant : constants){
			final Object con = constant.getValue();
				
			if(con instanceof Rational){
				final Rational iCon = (Rational) con;
				final String s = "Term con_" + iCon.hashCode() + " = Rational.valueOf(new BigInteger(\""+iCon.numerator().toString()+"\"),new BigInteger(\""+iCon.denominator().toString()+"\")).toTerm(sort_"+constant.getSort().getName()+");\n";
				sb.append(s);
				
			}else if(con instanceof BigInteger){
				final BigInteger iCon = (BigInteger) con;
				final String s = "Term con_" + iCon.hashCode() + " = script.numeral(\""+iCon.toString()+"\");\n";
				sb.append(s);
			
			}else if (con instanceof BigDecimal){
				final BigDecimal iCon = (BigDecimal) con;
				final String s = "Term con_" + iCon.hashCode() + " = script.decimal(\""+iCon.toString()+"\");\n";
				sb.append(s);
				
			}else if (con instanceof QuotedObject){
				final QuotedObject iCon = (QuotedObject) con;
				if(iCon.getValue() instanceof String){
					final String s = "Term con_" + iCon.hashCode() + " = script.string(\""+iCon.getValue()+"\");\n";
					sb.append(s);
					
				}else{
					throw new UnsupportedOperationException("I don't know what this is: " + iCon.getValue());
				}
			}else{
				throw new UnsupportedOperationException("I don't know what this is: " + con);
			}
		}
		sb.append("\n");
		
		//the vars
		sb.append("//Vars\n");
		for(final TermVariable var : vars){
			final String s = "TermVariable " + buildJavaVariableName(var) + " = script.variable(\"" + var.getName() + "\", sort_" + var.getSort().getName() + ");\n";
			sb.append(s);
		}
		sb.append("\n");
		
		
		//the functions
		sb.append("//Functions\n");
		for(final FunctionSymbol fun : funs){
			if(fun.isIntern()) {
				continue;
			}
			
			final StringBuilder param = new StringBuilder();
			param.append("new Sort[]{");
			if(fun.getParameterSorts().length>0){
				param.append("sort_" + fun.getParameterSorts()[0]);
				for (int i = 1; i < fun.getParameterSorts().length; i++) {
					param.append(", sort_" + fun.getParameterSorts()[i]);
					
				}
			}
			param.append("}");
			
			final String s = "script.declareFun(\"" + fun.getName() + "\", " + param.toString() + ", sort_" + fun.getReturnSort().getName() + ");\n";
			sb.append(s);
		}

		sb.append("\n");
		
		//the actual term
		sb.append("//term\n");
		sb.append("Term term = " + buildTerm(term) + ";");
		
		return sb.toString();
	}
	
	private void collect(final Term term){
		if (term instanceof ApplicationTerm) {
			final ApplicationTerm iTerm = (ApplicationTerm) term;
			sorts.add(iTerm.getSort());
			for (final Sort sort : iTerm.getFunction().getParameterSorts()) {
				sorts.add(sort);
			}
			funs.add(iTerm.getFunction());
			
			for (final Term t : iTerm.getParameters()) {
				collect(t);
			}
			
		} else if (term instanceof LetTerm) {
			final LetTerm iTerm = (LetTerm) term;
			sorts.add(iTerm.getSort());
			for (final TermVariable t : iTerm.getVariables()) {
				sorts.add(t.getSort()); //eventuell getDeclaredSort();
			}
			for(final TermVariable t : iTerm.getVariables()){
				vars.add(t);
			}
			
			for (final Term t : iTerm.getValues()) {
				collect(t);
			}
			collect(iTerm.getSubTerm());
			
		} else if (term instanceof AnnotatedTerm) {
			final AnnotatedTerm iTerm = (AnnotatedTerm) term;
			collect(iTerm.getSubterm());
			
		} else if (term instanceof QuantifiedFormula) {
			final QuantifiedFormula iTerm = (QuantifiedFormula) term;
			sorts.add(iTerm.getSort());
			for (final TermVariable t : iTerm.getVariables()) {
				sorts.add(t.getSort()); //eventuell getDeclaredSort();
			}
			for(final TermVariable t : iTerm.getVariables()){
				vars.add(t);
			}
			
			collect(iTerm.getSubformula());
			
		} else if (term instanceof ConstantTerm) {
			final ConstantTerm iTerm = (ConstantTerm) term;
			sorts.add(iTerm.getSort());
			constants.add(iTerm);

		} else if (term instanceof TermVariable) {
			final TermVariable iTerm = (TermVariable) term;
			sorts.add(iTerm.getSort()); //eventuell getDeclaredSort();
			vars.add(iTerm);
		}
	}
	
	private String buildTerm(final Term term){
		final StringBuilder sb = new StringBuilder();
		if (term instanceof ApplicationTerm) {
			final ApplicationTerm iTerm = (ApplicationTerm) term;
			
			sb.append("script.term(\"" + iTerm.getFunction().getName() + "\"");
			for(final Term t : iTerm.getParameters()){
				sb.append(", "+buildTerm(t));
			}
			sb.append(")");
		} else if (term instanceof LetTerm) {
			final LetTerm iTerm = (LetTerm) term;
			
			sb.append("script.let(");
			
			
			sb.append("new TermVariable[]{");
			if(iTerm.getVariables().length>0){
				sb.append(buildJavaVariableName(iTerm.getVariables()[0]));
				for (int i = 1; i < iTerm.getVariables().length; i++) {
					sb.append(", " + buildJavaVariableName(iTerm.getVariables()[0]));
				}
			}
			sb.append("}, new Term[]{");
			
			if(iTerm.getValues().length>0){
				sb.append(buildTerm(iTerm.getValues()[0]));
				for (int i = 1; i < iTerm.getValues().length; i++) {
					sb.append(", "+ buildTerm(iTerm.getValues()[i]));
				}
			}
			sb.append("}, " + buildTerm(iTerm.getSubTerm()) + ")");
			
		} else if (term instanceof AnnotatedTerm) {
			final AnnotatedTerm iTerm = (AnnotatedTerm) term;
			
			sb.append(buildTerm(iTerm.getSubterm()));

		} else if (term instanceof QuantifiedFormula) {
			final QuantifiedFormula iTerm = (QuantifiedFormula) term;
			
			sb.append("script.quantifier(" + iTerm.getQuantifier() + ", ");
			
			sb.append("new TermVariable[]{");
			if(iTerm.getVariables().length > 0){
				sb.append(buildJavaVariableName(iTerm.getVariables()[0]));
				for (int i = 0; i < iTerm.getVariables().length; i++) {
					sb.append(", "+ buildJavaVariableName(iTerm.getVariables()[0]));
				}
			}
			sb.append("}, ");
			
			sb.append(buildTerm(iTerm.getSubformula()));
			sb.append(")");

		} else if (term instanceof ConstantTerm) {
			final ConstantTerm iTerm = (ConstantTerm) term;
			
			sb.append("con_" + iTerm.getValue().hashCode());
			
		} else if (term instanceof TermVariable) {
			final TermVariable iTerm = (TermVariable) term;

			sb.append(buildJavaVariableName(iTerm));
		}
		return sb.toString();
	}
	
	private static String buildJavaVariableName(final TermVariable tv) {
		//TODO 2016-12-21 Matthias: Think about better escaping
		return "var_" + tv.getName().replaceAll("[.()#~]", "");
		
	}

}
