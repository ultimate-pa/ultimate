/*
 * Copyright (C) 2012-2015 Evren Ermis
 * Copyright (C) 2015 Matthias Heizmann (heizmann@informatik.uni-freiburg.de)
 * Copyright (C) 2012-2015 University of Freiburg
 * 
 * This file is part of the ULTIMATE ModelCheckerUtils Library.
 * 
 * The ULTIMATE ModelCheckerUtils Library is free software: you can redistribute it and/or modify
 * it under the terms of the GNU Lesser General Public License as published
 * by the Free Software Foundation, either version 3 of the License, or
 * (at your option) any later version.
 * 
 * The ULTIMATE ModelCheckerUtils Library is distributed in the hope that it will be useful,
 * but WITHOUT ANY WARRANTY; without even the implied warranty of
 * MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
 * GNU Lesser General Public License for more details.
 * 
 * You should have received a copy of the GNU Lesser General Public License
 * along with the ULTIMATE ModelCheckerUtils Library. If not, see <http://www.gnu.org/licenses/>.
 * 
 * Additional permission under GNU GPL version 3 section 7:
 * If you modify the ULTIMATE ModelCheckerUtils Library, or any covered work, by linking
 * or combining it with Eclipse RCP (or a modified version of Eclipse RCP), 
 * containing parts covered by the terms of the Eclipse Public License, the 
 * licensors of the ULTIMATE ModelCheckerUtils Library grant you additional permission 
 * to convey the resulting work.
 */
package de.uni_freiburg.informatik.ultimate.plugins.generator.codecheck;

import java.util.ArrayList;

import de.uni_freiburg.informatik.ultimate.logic.AnnotatedTerm;
import de.uni_freiburg.informatik.ultimate.logic.Annotation;
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
	
	@Override
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
			final AnnotatedTerm annotatedTerm = (AnnotatedTerm)term;
			for (final Annotation annotation: annotatedTerm.getAnnotations()) {
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
