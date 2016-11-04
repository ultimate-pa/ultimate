package de.uni_freiburg.informatik.ultimate.modelcheckerutils.smt.bdd;

import java.util.ArrayList;
import java.util.List;

import de.uni_freiburg.informatik.ultimate.logic.AnnotatedTerm;
import de.uni_freiburg.informatik.ultimate.logic.ApplicationTerm;
import de.uni_freiburg.informatik.ultimate.logic.ConstantTerm;
import de.uni_freiburg.informatik.ultimate.logic.LetTerm;
import de.uni_freiburg.informatik.ultimate.logic.QuantifiedFormula;
import de.uni_freiburg.informatik.ultimate.logic.Term;
import de.uni_freiburg.informatik.ultimate.logic.TermVariable;
import net.sf.javabdd.BDD;
import net.sf.javabdd.BDDFactory;

public class BDDBuilderRecursive {
	public BDD buildRecursive(Term t, List<Term> atoms){
	BDDFactory factory = BDDFactory.init("java", atoms.size()+2, atoms.size()+2, false);
	factory.setVarNum(atoms.size());
	return buildRecursive2(t, factory, atoms);
}

private BDD buildRecursive2(Term t, BDDFactory factory, List<Term> atoms){
	if (t instanceof ApplicationTerm) {
		ApplicationTerm term = (ApplicationTerm)t;
		String fName = term.getFunction().getName();
		if(fName.equals("and") || fName.equals("or") || fName.equals("xor") || fName.equals("not") || fName.equals("=>")){
			List<BDD> params = new ArrayList<BDD>();
			for(Term th:term.getParameters()){
				params.add(buildRecursive2(th, factory, atoms));
			}
			
			if(fName.equals("and")){
				BDD result = params.remove(0);
				for (BDD bdd : params) {
					result = result.and(bdd);
				}
				return result;
			}else if(fName.equals("or")){
				BDD result = params.remove(0);
				for (BDD bdd : params) {
					result = result.or(bdd);
				}
				return result;
			}else if(fName.equals("xor")){
				BDD result = params.remove(0);
				for (BDD bdd : params) {
					result = result.xor(bdd);
				}
				return result;
			}else if(fName.equals("=>")){
				BDD result = params.remove(0);
				for (BDD bdd : params) {
					result = result.imp(bdd);
				}
				return result;
			}else if(fName.equals("not")){
				return params.get(0).not();
			}
		}else if(fName.equals("true")){
			return factory.one();
			
		}else if(fName.equals("false")){
			return factory.zero();
			
		}else{
			return factory.ithVar(atoms.indexOf(term));
		}
	} else if (t instanceof LetTerm) {
		return factory.ithVar(atoms.indexOf(t));
		
	} else if (t instanceof AnnotatedTerm) {
		return buildRecursive2(((AnnotatedTerm)t).getSubterm(), factory, atoms);
		
	} else if (t instanceof QuantifiedFormula) {
		return factory.ithVar(atoms.indexOf(t));
		
	} else if (t instanceof ConstantTerm) {
		return factory.ithVar(atoms.indexOf(t));
		
	} else if (t instanceof TermVariable) {
		return factory.ithVar(atoms.indexOf(t));
		
	}
	
	throw new UnsupportedOperationException(t.toString());
}
}
