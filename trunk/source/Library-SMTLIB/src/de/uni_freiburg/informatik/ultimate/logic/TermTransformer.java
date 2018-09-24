/*
 * Copyright (C) 2009-2012 University of Freiburg
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
package de.uni_freiburg.informatik.ultimate.logic;

import java.util.ArrayDeque;
import java.util.Arrays;
import java.util.HashMap;

/**
 * This is the base class for transforming formulas.  It does nothing by itself
 * but you can use it to create arbitrary transformations on formulas.
 * The transform method applies the transformation in a non-recursive manner.
 *
 * Subclasses should override the function convert.  It takes as argument
 * the term to convert and should set its result with setResult.  If it needs
 * to build a more complex term with transformed arguments, it can enqueue the
 * subclasses BuildLetTerm, BuildApplicationTerm, BuildAnnotatedTerm with
 * enqueueWalker.  The arguments should be added to the work queue by
 * pushTerm/pushTerms.
 *
 * Of course, you can also add your own Build class that takes the converted
 * arguments from the conversion stack using getConverted().
 *
 * @author Jochen Hoenicke
 */
public class TermTransformer extends NonRecursive {
	/**
	 * The term cache.
	 */
	private final ArrayDeque<HashMap<Term, Term>> mCache =
		new ArrayDeque<HashMap<Term,Term>>();

	/**
	 * The converted terms.  This is used for example to store the
	 * arguments of an application term, before the application term is
	 * evaluated.
	 */
	private final ArrayDeque<Term> mConverted = new ArrayDeque<Term>();

	/**
	 * The converted object arrays. This is used to store the arguments of an array valued annotation, before the
	 * annotation's subterm is processed.
	 */
	private final ArrayDeque<Object[]> mConvertedArrays = new ArrayDeque<Object[]>();

	/**
	 * This class represents one item of work. It consists of a term and some task that still needs to be performed on
	 * the term.
	 */
	private static class Convert implements Walker {
		private final Term mTerm;
		public Convert(final Term term) {
			mTerm = term;
		}

		@Override
		public String toString() {
			return "Convert " + mTerm.toStringDirect();
		}

		@Override
		public void walk(final NonRecursive walker) {
			((TermTransformer) walker).cacheConvert(mTerm);
		}
	}

	/**
	 * Push all terms in the array on the todo stack as CONVERT work item.
	 * @param terms the array of terms.
	 */
	protected final void pushTerms(final Term[] terms) {
		for (int i = terms.length - 1; i >= 0; i--) {
			pushTerm(terms[i]);
		}
	}

	/**
	 * Push a term on the todo stack as CONVERT work item.
	 * @param term the term to convert.
	 */
	protected final void pushTerm(final Term term) {
		enqueueWalker(new Convert(term));
	}

	/**
	 * Set the conversion result to term.
	 * @param term the converted term.
	 */
	protected final void setResult(final Term term) {
		mConverted.addLast(term);
	}

	private static class AddCache implements Walker {
		Term mOldTerm;
		public AddCache(final Term term) {
			mOldTerm = term;
		}
		@Override
		public void walk(final NonRecursive engine) {
			final TermTransformer transformer = (TermTransformer) engine;
			transformer.mCache.getLast().put(
					mOldTerm, transformer.mConverted.getLast());
		}

		@Override
		public String toString() {
			return "AddCache[" + mOldTerm.toStringDirect() + "]";
		}
	}

	private void cacheConvert(final Term term) {
		final Term result = mCache.getLast().get(term);
		if (result == null) {
			enqueueWalker(new AddCache(term));
			convert(term);
		} else {
			setResult(result);
		}
	}

	protected void beginScope() {
		mCache.addLast(new HashMap<Term, Term>());
	}

	protected void endScope() {
		mCache.removeLast();
	}

	/**
	 * The function that does the transformation.   Override this function
	 * if you build your own term transformer.  It does not return the result
	 * but instead it puts it on the converted stack using setResult().
	 * Instead it can also enqueue some Builders that will in the end put the
	 * result on the converted stack.
	 *
	 * You can always call super.convert() if you do not need to convert
	 * the term.  It will still convert the sub-terms. If you do not want to
	 * convert the sub terms, call setResult(term) instead.
	 * @param term  The term to convert.
	 */
	protected void convert(final Term term) {
		if (term instanceof ConstantTerm
			|| term instanceof TermVariable) {
			mConverted.addLast(term);
		} else if (term instanceof ApplicationTerm) {
			enqueueWalker(new BuildApplicationTerm((ApplicationTerm) term));
			pushTerms(((ApplicationTerm) term).getParameters());
		} else if (term instanceof LetTerm) {
			enqueueWalker(new StartLetTerm((LetTerm) term));
			pushTerms(((LetTerm) term).getValues());
		} else if (term instanceof QuantifiedFormula) {
			enqueueWalker(new BuildQuantifier((QuantifiedFormula) term));
			pushTerm(((QuantifiedFormula) term).getSubformula());
			beginScope();
		} else if (term instanceof AnnotatedTerm) {
			final AnnotatedTerm annterm = (AnnotatedTerm) term;
			enqueueWalker(new BuildAnnotation(annterm));
			final ArrayDeque<Object> todo = new ArrayDeque<>();
			for (Annotation annot : annterm.getAnnotations()) {
				if (annot.getValue() != null) {
					todo.add(annot.getValue());
				}
			}
			while (!todo.isEmpty()) {
				Object value = todo.removeLast();
				if (value instanceof Term) {
					pushTerm((Term) value);
				} else if (value instanceof Object[]) {
					enqueueWalker(new BuildObjectArray((Object[]) value));
					for (Object elem : (Object[]) value) {
						todo.add(elem);
					}
				}
			}
			pushTerm(annterm.getSubterm());
			return;
		} else {
			throw new AssertionError("Unknown Term: " + term.toStringDirect());
		}
	}

	public void convertApplicationTerm(
			final ApplicationTerm appTerm, final Term[] newArgs) {
		Term newTerm = appTerm;
		if (newArgs != appTerm.getParameters()) {
			final FunctionSymbol fun = appTerm.getFunction();
			final Theory theory = fun.getTheory();
			newTerm = theory.term(fun, newArgs);
		}
		setResult(newTerm);
	}

	public void preConvertLet(final LetTerm oldLet, final Term[] newValues) {
		beginScope();
		enqueueWalker(new BuildLetTerm(oldLet, newValues));
		pushTerm(oldLet.getSubTerm());
	}

	public void postConvertLet(final LetTerm oldLet, final Term[] newValues, final Term newBody) {
		Term result = oldLet;
		if (oldLet.getValues() != newValues
			|| oldLet.getSubTerm() != newBody) {
			result = oldLet.getTheory().let(
					oldLet.getVariables(), newValues, newBody);
		}
		setResult(result);
	}

	public void postConvertQuantifier(final QuantifiedFormula old, final Term newBody) {
		Term newFormula = old;
		if (newBody != old.getSubformula()) {
			final Theory theory = old.getTheory();
			final TermVariable[] vars = old.getVariables();
			newFormula = old.getQuantifier() == QuantifiedFormula.EXISTS
				? theory.exists(vars, newBody) : theory.forall(vars,newBody);
		}
		setResult(newFormula);
	}

	public void postConvertAnnotation(final AnnotatedTerm old,
			final Annotation[] newAnnots, final Term newBody) {
		final Annotation[] annots = old.getAnnotations();
		Term result = old;
		if (newBody != old.getSubterm()	|| newAnnots != annots) {
			result = old.getTheory().annotatedTerm(newAnnots, newBody);
		}
		setResult(result);
	}

	/**
	 * Transform a term.
	 * @param term the term to transform.
	 * @return the resulting transformed term.
	 */
	public final Term transform(final Term term) {
		beginScope();
		run(new Convert(term));
		endScope();
		return mConverted.removeLast();
	}

	/**
	 * Get a single converted term from the converted stack.  This is the
	 * dual of pushTerm() that is called after the term were removed
	 * from the todo stack and pushed to the converted stack.
	 * @return the new converted term.
	 */
	protected final Term getConverted() {
		return mConverted.removeLast();
	}

	/**
	 * Get a single converted object array from the converted stack.
	 * 
	 * @return the new converted object array.
	 */
	protected final Object[] getConvertedObjectArray() {
		return mConvertedArrays.removeLast();
	}

	/**
	 * Get the converted terms from the converted stack. This is the dual of pushTerms() that is called after the term
	 * were removed from the todo stack and pushed to the converted stack. It takes the old terms as argument and checks
	 * for changes.
	 * 
	 * @param oldArgs
	 *            the original arguments.
	 * @return the new converted arguments. It will return the same array oldArgs if there were no changes.
	 */
	protected final Term[] getConverted(final Term[] oldArgs) {
		Term[] newArgs = oldArgs;
		for (int i = oldArgs.length - 1; i >= 0; i--) {
			final Term newTerm = getConverted();
			if (newTerm != oldArgs[i]) {
				if (newArgs == oldArgs) {
					newArgs = oldArgs.clone();
				}
				newArgs[i] = newTerm;
			}
		}
		return newArgs;
	}

	/**
	 * Collect the arguments of an application term from the converted stack
	 * and finish the conversion of appTerm.  This is called after the arguments
	 * of appTerm have been converted.  It will put the converted term on
	 * the converted stack and store it in the cache.
	 */
	protected static class BuildApplicationTerm implements Walker {
		/** the application term to convert. */
		private final ApplicationTerm mAppTerm;

		public BuildApplicationTerm(final ApplicationTerm term) {
			mAppTerm = term;
		}

		@Override
		public void walk(final NonRecursive engine) {
			final TermTransformer transformer = (TermTransformer) engine;
			/* collect args and check if they have been changed */
			final Term[] oldArgs = mAppTerm.getParameters();
			final Term[] newArgs = transformer.getConverted(oldArgs);
			transformer.convertApplicationTerm(mAppTerm, newArgs);
		}

		@Override
		public String toString() {
			return mAppTerm.getFunction().getApplicationString();
		}
	}

	/**
	 * Walker that is called after the variable values are transformed
	 * and before the let body starts.
	 */
	protected static class StartLetTerm implements Walker {
		/** the let term to convert. */
		private final LetTerm mLetTerm;

		public StartLetTerm(final LetTerm term) {
			mLetTerm = term;
		}

		@Override
		public void walk(final NonRecursive engine) {
			final TermTransformer transformer = (TermTransformer) engine;
			final Term[] values = transformer.getConverted(mLetTerm.getValues());
			transformer.preConvertLet(mLetTerm, values);
		}

		@Override
		public String toString() {
			return "let" + Arrays.toString(mLetTerm.getVariables());
		}
	}

	/**
	 * Collect the sub term and the values of a let term from the
	 * converted stack and finish the conversion of let term.
	 */
	protected static class BuildLetTerm implements Walker {
		/** the let term to convert. */
		private final LetTerm mLetTerm;
		/** the converted values that are letted to the variables. */
		private final Term[] mNewValues;

		public BuildLetTerm(final LetTerm term, final Term[] newValues) {
			mLetTerm = term;
			mNewValues = newValues;
		}

		@Override
		public void walk(final NonRecursive engine) {
			final TermTransformer transformer = (TermTransformer) engine;
			final Term newBody = transformer.getConverted();
			transformer.postConvertLet(mLetTerm, mNewValues, newBody);
			transformer.endScope();
		}

		@Override
		public String toString() {
			return "let" + Arrays.toString(mLetTerm.getVariables());
		}
	}

	/**
	 * Collect the sub term of a quantified formula and build the converted
	 * formula.  The converted sub formula is expected to be on the
	 * converted stack.
	 * It stores the converted quantifier on the converted stack and in the
	 * cache.
	 */
	protected static class BuildQuantifier implements Walker {
		/** the quantifier to convert. */
		private final QuantifiedFormula mQuant;

		public BuildQuantifier(final QuantifiedFormula term) {
			mQuant = term;
		}

		@Override
		public void walk(final NonRecursive engine) {
			final TermTransformer transformer = (TermTransformer) engine;
			final Term sub = transformer.getConverted();
			transformer.postConvertQuantifier(mQuant, sub);
			transformer.endScope();
		}

		@Override
		public String toString() {
			return mQuant.getQuantifier() == QuantifiedFormula.EXISTS
					? "exists" : "forall";
		}
	}

	/**
	 * Collect the sub term and annotations of an annotated formula from
	 * the converted stack.  It converts the annotation and stores the
	 * result in the cache and on the converted stack.
	 * Note that only Annotations that are of type Term or Term[] are
	 * converted.
	 */
	protected static class BuildAnnotation implements Walker {
		/** the annotated term. */
		private final AnnotatedTerm mAnnotatedTerm;

		public BuildAnnotation(final AnnotatedTerm term) {
			mAnnotatedTerm = term;
		}

		@Override
		public void walk(final NonRecursive engine) {
			final TermTransformer transformer = (TermTransformer) engine;
			final Annotation[] annots = mAnnotatedTerm.getAnnotations();
			Annotation[] newAnnots = annots;
			for (int i = annots.length - 1; i >= 0; i--) {
				final Object value = annots[i].getValue();
				Object newValue;
				if (value instanceof Term) {
					newValue = transformer.getConverted();
				} else if (value instanceof Object[]) {
					newValue = transformer.getConvertedObjectArray();
				} else {
					newValue = value;
				}
				if (newValue != value) {
					if (annots == newAnnots) {
						newAnnots = annots.clone();
					}
					newAnnots[i] = new Annotation(annots[i].getKey(), newValue);
				}
			}
			final Term sub = transformer.getConverted();
			transformer.postConvertAnnotation(mAnnotatedTerm, newAnnots, sub);
		}

		@Override
		public String toString() {
			return "annotate";
		}
	}

	/**
	 * Collect the sub terms and sub arrays of an array (part of an annotated formula).
	 */
	protected static class BuildObjectArray implements Walker {
		private final Object[] mArray;

		public BuildObjectArray(final Object[] array) {
			mArray = array;
		}

		@Override
		public void walk(final NonRecursive engine) {
			final TermTransformer transformer = (TermTransformer) engine;
			Object[] newArray = mArray;
			for (int i = newArray.length - 1; i >= 0; i--) {
				final Object value = newArray[i];
				Object newValue;
				if (value instanceof Term) {
					newValue = transformer.getConverted();
				} else if (value instanceof Object[]) {
					newValue = transformer.getConvertedObjectArray();
				} else {
					newValue = value;
				}
				if (newValue != value) {
					if (mArray == newArray) {
						newArray = mArray.clone();
					}
					newArray[i] = newValue;
				}
			}
			transformer.mConvertedArrays.addLast(newArray);
		}

		@Override
		public String toString() {
			return "annotate";
		}
	}

	@Override
	public void reset() {
		super.reset();
		mConverted.clear();
		mCache.clear();
	}
}
