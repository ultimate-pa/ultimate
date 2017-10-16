/*
 * Copyright (C) 2012 University of Freiburg
 *
 * This file is part of SMTInterpol.
 *
 * SMTInterpol is free software: you can redistribute it and/or modify
 * it under the terms of the GNU Lesser General Public License as published
 * by the Free Software Foundation, either version 3 of the License, or
 * (at your option) any later version.
 *
 * SMTInterpol is distributed in the hope that it will be useful,
 * but WITHOUT ANY WARRANTY; without even the implied warranty of
 * MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
 * GNU Lesser General Public License for more details.
 *
 * You should have received a copy of the GNU Lesser General Public License
 * along with SMTInterpol.  If not, see <http://www.gnu.org/licenses/>.
 */
package de.uni_freiburg.informatik.ultimate.smtinterpol.smtlib2;

import de.uni_freiburg.informatik.ultimate.logic.AnnotatedTerm;
import de.uni_freiburg.informatik.ultimate.logic.Annotation;
import de.uni_freiburg.informatik.ultimate.logic.ApplicationTerm;
import de.uni_freiburg.informatik.ultimate.logic.FunctionSymbol;
import de.uni_freiburg.informatik.ultimate.logic.NonRecursive;
import de.uni_freiburg.informatik.ultimate.logic.Rational;
import de.uni_freiburg.informatik.ultimate.logic.Term;
import de.uni_freiburg.informatik.ultimate.logic.TermTransformer;

/**
 * This class can be used to replace the symbols @/0, @div0, and @mod0 from
 * terms and replace them by their meaning (/ ... 0), (div ... 0), and
 * (mod ... 0).
 *
 * This transformer also tries to transform annotations to remove these terms.
 * This is needed to fix the proof trees returned from SMTInterpol.  Note that
 * in these proof terms annotations might be Object[] that contain further terms
 * or Term[]s.
 * @author Juergen Christ
 */
public class Div0Remover extends TermTransformer {

	private static class BuildAnnotationTerm implements Walker {
		private final AnnotatedTerm mTerm;

		public BuildAnnotationTerm(final AnnotatedTerm term) {
			mTerm = term;
		}
		@Override
		public void walk(final NonRecursive engine) {
			final Div0Remover remover = (Div0Remover) engine;
			final Annotation[] newAnnots =
					remover.collectAnnotations(mTerm.getAnnotations());
			final Term sub = remover.getConverted();
			if (newAnnots == mTerm.getAnnotations() && sub == mTerm.getSubterm()) {
				remover.setResult(mTerm);
			} else {
				remover.setResult(
						mTerm.getTheory().annotatedTerm(newAnnots, sub));
			}
		}

	}

	private void pushTermsFromArray(final Object[] arr) {
		for (int i = arr.length - 1; i >= 0; --i) {
			final Object val = arr[i];
			if (val instanceof Term) {
				pushTerm((Term) val);
			} else if (val instanceof Term[]) {
				pushTerms((Term[]) val);
			} else if (val instanceof Object[]) {
				/* Recursion should be okay here since nesting should not be too
				 * big.
				 */
				pushTermsFromArray((Object[]) val);
			}
		}
	}

	void pushTermsFromAnnotations(final Annotation[] annots) {
		for (int i = annots.length - 1; i >= 0; --i) {
			final Object val = annots[i].getValue();
			if (val instanceof Term) {
				pushTerm((Term) val);
			} else if (val instanceof Term[]) {
				pushTerms((Term[]) val);
			} else if (val instanceof Object[]) {
				pushTermsFromArray((Object[]) val);
			}
		}
	}

	private Object[] getFromArray(final Object[] oldVal) {
		Object[] newVal = oldVal;
		for (int i = oldVal.length - 1; i >= 0; --i) {
			final Object val = oldVal[i];
			Object newValue;
			if (val instanceof Term) {
				newValue = getConverted();
			} else if (val instanceof Term[]) {
				newValue = getConverted((Term[]) val);
			} else if (val instanceof Object[]) {
				/* Recursion should be okay here since nesting should not be too
				 * big.
				 */
				newValue = getFromArray((Object[]) val);
			} else {
				newValue = val;
			}
			if (newValue != val) {
				if (newVal == oldVal) {
					newVal = oldVal.clone();
				}
				newVal[i] = newValue;
			}
		}
		return newVal;
	}

	Annotation[] collectAnnotations(final Annotation[] oldAnnots) {
		Annotation[] newAnnots = oldAnnots;
		for (int i = oldAnnots.length - 1; i >= 0; i--) {
			final Object value = oldAnnots[i].getValue();
			Object newValue;
			if (value instanceof Term) {
				newValue = getConverted();
			} else if (value instanceof Term[]) {
				newValue = getConverted((Term[]) value);
			} else if (value instanceof Object[]) {
				newValue = getFromArray((Object[]) value);
			} else {
				newValue = value;
			}
			if (newValue != value) {
				if (oldAnnots == newAnnots) {
					newAnnots = oldAnnots.clone();
				}
				newAnnots[i] = new Annotation(oldAnnots[i].getKey(), newValue);
			}
		}
		return newAnnots;
	}

	@Override
	protected void convert(final Term term) {
		if (term instanceof AnnotatedTerm) {
			/* We cannot use postConvertAnnotation here since TermTransformer
			 * does not descend into Object[] which is needed for proof tree
			 * transformations.
			 */
			final AnnotatedTerm annot = (AnnotatedTerm) term;
			enqueueWalker(new BuildAnnotationTerm(annot));
			pushTermsFromAnnotations(annot.getAnnotations());
			pushTerm(annot.getSubterm());
			return;
		}
		super.convert(term);
	}

	@Override
	public void convertApplicationTerm(final ApplicationTerm appTerm, final Term[] newArgs) {
		final FunctionSymbol sym = appTerm.getFunction();
		String name = sym.getName();
		if (name.charAt(0) == '@' && name.endsWith("0")) {
			name = name.substring(1, name.length() - 1);
			final Term[] args = new Term[2];
			args[0] = newArgs[0];
			args[1] = Rational.ZERO.toTerm(newArgs[0].getSort());
			setResult(appTerm.getTheory().term(name, args));
		} else {
			super.convertApplicationTerm(appTerm, newArgs);
		}
	}
}
