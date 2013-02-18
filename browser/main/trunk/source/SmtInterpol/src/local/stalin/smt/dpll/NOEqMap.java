package local.stalin.smt.dpll;

import java.util.HashMap;
import java.util.Map;

import local.stalin.logic.ApplicationTerm;
import local.stalin.logic.Term;
import local.stalin.logic.Theory;

public class NOEqMap extends HashMap<Term,Term> {
	private static final long serialVersionUID = -7577361041831889065L;
	private Theory mtheory;
	
	public NOEqMap(Theory theory) {
		mtheory = theory;
	}
	public Term put(Term key,Term value) {
		return super.put(key,substitute(key,value));
	}
	private Term substitute(Term key,Term value) {
		Term newvalue = subsituteValue(value);
		mergeEqs(key,newvalue);
		return newvalue;
	}
	private Term merge(Term val,Term part,Term subst) {
		if( val == part )
			return subst;
		else if( val instanceof ApplicationTerm ) {
			ApplicationTerm at = (ApplicationTerm)val;
			Term[] parameters = at.getParameters();
			if( parameters.length == 0 )
				return val;
			for( int i = 0; i < parameters.length; ++i )
				parameters[i] = merge(parameters[i],part,subst);
			return mtheory.term(at.getFunction(), parameters);
		} else
			return val;
	}
	private void mergeEqs(Term key,Term value) {
		for( Map.Entry<Term,Term> me : entrySet() ) {
			me.setValue(merge(me.getValue(),key,value));
		}
	}
	private Term subsituteValue(Term value) {
		Term res = get(value);
		if( res != null )
			return res;
		else if( value instanceof ApplicationTerm ) {
			ApplicationTerm at = (ApplicationTerm)value;
			Term[] parameter = at.getParameters();
			if( parameter.length == 0 )
				return value;
			for( int i = 0; i < parameter.length; ++i )
				parameter[i] = subsituteValue(parameter[i]);
			return mtheory.term(at.getFunction(),parameter);
		} else 
			return value;
	}
}
