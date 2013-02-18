package de.uni_freiburg.informatik.ultimate.modelcheckerutils.transfomers;

import java.util.ArrayList;

import de.uni_freiburg.informatik.ultimate.logic.AnnotatedTerm;
import de.uni_freiburg.informatik.ultimate.logic.Annotation;
import de.uni_freiburg.informatik.ultimate.logic.ApplicationTerm;
import de.uni_freiburg.informatik.ultimate.logic.Term;
import de.uni_freiburg.informatik.ultimate.logic.TermTransformer;

/*
 * This class collects all terms in the given term that are annotated with
 * a location. This class is used in the safety checker plugin in order to
 * get the array of all locations along the feasible error trace.
 */
public class AnnotatedTermsCollector extends TermTransformer {

	/*
	 * Collection of all annotated terms in the given term
	 */
	ArrayList<AnnotatedTerm> mAnnotatedTerms = new ArrayList<AnnotatedTerm>();
	
	/*
	 * (non-Javadoc)
	 * @see de.uni_freiburg.informatik.ultimate.logic.TermTransformer#convert(de.uni_freiburg.informatik.ultimate.logic.Term)
	 */
	
	protected void convert(Term term) {
//		if (term instanceof ApplicationTerm) {
//			ApplicationTerm appTerm = (ApplicationTerm)term;
//			for (int i = 0; i < appTerm.getParameters().length; i++) {
//				convert(appTerm.getParameters()[i]);
//			}
//			super.convertApplicationTerm(appTerm, appTerm.getParameters());
//			return;
//		} else 
		if (term instanceof AnnotatedTerm) {
			AnnotatedTerm annotatedTerm = (AnnotatedTerm)term;
			for (Annotation annotation: annotatedTerm.getAnnotations()) {
				if (annotation.getKey().equals(":location")) {
					mAnnotatedTerms.add(annotatedTerm);
					super.setResult(term);
					return;
				}
			}
		}
		super.convert(term);
	}
	
	public ArrayList<AnnotatedTerm> getAnnotatedTerms() {
		return mAnnotatedTerms;
	}
	
}
