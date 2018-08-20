package de.uni_freiburg.informatik.ultimate.icfgtransformer.heapseparator.transformers;

import java.util.ArrayDeque;
import java.util.Arrays;

import de.uni_freiburg.informatik.ultimate.icfgtransformer.heapseparator.datastructures.SubtreePosition;
import de.uni_freiburg.informatik.ultimate.logic.AnnotatedTerm;
import de.uni_freiburg.informatik.ultimate.logic.Annotation;
import de.uni_freiburg.informatik.ultimate.logic.ApplicationTerm;
import de.uni_freiburg.informatik.ultimate.logic.ConstantTerm;
import de.uni_freiburg.informatik.ultimate.logic.FunctionSymbol;
import de.uni_freiburg.informatik.ultimate.logic.LetTerm;
import de.uni_freiburg.informatik.ultimate.logic.NonRecursive;
import de.uni_freiburg.informatik.ultimate.logic.QuantifiedFormula;
import de.uni_freiburg.informatik.ultimate.logic.Term;
import de.uni_freiburg.informatik.ultimate.logic.TermTransformer;
import de.uni_freiburg.informatik.ultimate.logic.TermVariable;
import de.uni_freiburg.informatik.ultimate.logic.Theory;

/**
 * A variant of {@link TermTransformer} that carries around {@link SubtreePosition} objects, so the transformation can
 * transform the same {@link Term} at different positions in the formula differently.
 * <p>
 * Note that this may cause exponential blowup if there is sharing in the input term.
 * <p>
 * (In contrast to {@link TermTransformer}, this class has no cache, as it is unclear how that would work.)
 * <p>
 * (Much of the code here is a copy of code in {@link TermTransformer} with only slight changes.)
 *
 * @author Alexander Nutz (nutz@informatik.uni-freiburg.de)
 */
class PositionAwareTermTransformer extends NonRecursive {

	/**
	 * The converted terms.  This is used for example to store the
	 * arguments of an application term, before the application term is
	 * evaluated.
	 */
	private final ArrayDeque<Term> mConverted = new ArrayDeque<Term>();

	/**
	 * This class represents one item of work.  It consists of a term and
	 * some task that still needs to be performed on the term.
	 */
	private static class Convert implements Walker {
		private final Term mTerm;
		private final SubtreePosition mPos;
		public Convert(final Term term, final SubtreePosition pos) {
			mTerm = term;
			mPos = pos;
		}

		@Override
		public String toString() {
			return "Convert " + mTerm.toStringDirect();
		}

		@Override
		public void walk(final NonRecursive walker) {
			((PositionAwareTermTransformer) walker).convert(mTerm, mPos);
		}
	}

	/**
	 * Push all terms in the array on the todo stack as CONVERT work item.
	 * @param terms the array of terms.
	 */
	protected final void pushTerms(final Term[] terms, final SubtreePosition pos) {
		for (int i = terms.length - 1; i >= 0; i--) {
			pushTerm(terms[i], pos.append(i));
		}
	}

	/**
	 * Push a term on the todo stack as CONVERT work item.
	 * @param term the term to convert.
	 */
	protected final void pushTerm(final Term term, final SubtreePosition pos) {
		enqueueWalker(new Convert(term, pos));
	}

	/**
	 * Set the conversion result to term.
	 * @param term the converted term.
	 */
	protected final void setResult(final Term term) {
		mConverted.addLast(term);
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
	protected void convert(final Term term, final SubtreePosition pos) {
		if (term instanceof ConstantTerm
			|| term instanceof TermVariable) {
			mConverted.addLast(term);
		} else if (term instanceof ApplicationTerm) {
			enqueueWalker(new BuildApplicationTerm((ApplicationTerm) term, pos));
			pushTerms(((ApplicationTerm) term).getParameters(), pos);
		} else if (term instanceof LetTerm) {
			enqueueWalker(new StartLetTerm((LetTerm) term, pos));
			pushTerms(((LetTerm) term).getValues(), pos);
		} else if (term instanceof QuantifiedFormula) {
			enqueueWalker(new BuildQuantifier((QuantifiedFormula) term, pos));
			pushTerm(((QuantifiedFormula) term).getSubformula(), pos.append(0));
			beginScope();
		} else if (term instanceof AnnotatedTerm) {
			final AnnotatedTerm annterm = (AnnotatedTerm) term;
			enqueueWalker(new BuildAnnotation(annterm, pos));
			final Annotation[] annots = annterm.getAnnotations();
			for (int i = annots.length - 1; i >= 0; i--) {
				final Object value = annots[i].getValue();
				if (value instanceof Term) {
					pushTerm((Term) value, pos.append(i));
				} else if (value instanceof Term[]) {
					pushTerms((Term[]) value, pos.append(i));
				}
			}
			pushTerm(annterm.getSubterm(), pos.append(annots.length));
			return;
		} else {
			throw new AssertionError("Unknown Term: " + term.toStringDirect());
		}
	}

	public void convertApplicationTerm(
			final ApplicationTerm appTerm, final Term[] newArgs, final SubtreePosition pos) {
		Term newTerm = appTerm;
		if (newArgs != appTerm.getParameters()) {
			final FunctionSymbol fun = appTerm.getFunction();
			final Theory theory = fun.getTheory();
			newTerm = theory.term(fun, newArgs);
		}
		setResult(newTerm);
	}

	public void preConvertLet(final LetTerm oldLet, final Term[] newValues, final SubtreePosition pos) {
		beginScope();
		enqueueWalker(new BuildLetTerm(oldLet, newValues, pos));
		pushTerm(oldLet.getSubTerm(), pos);
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

	protected void beginScope() {
//		mCache.addLast(new HashMap<Term, Term>());
	}

	protected void endScope() {
//		mCache.removeLast();
	}

	/**
	 * Transform a term.
	 * @param term the term to transform.
	 * @return the resulting transformed term.
	 */
	public final Term transform(final Term term) {
		beginScope();
		run(new Convert(term, new SubtreePosition()));
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
	 * Get the converted terms from the converted stack.  This is the
	 * dual of pushTerms() that is called after the term were removed
	 * from the todo stack and pushed to the converted stack.  It takes
	 * the old terms as argument and checks for changes.
	 * @param oldArgs the original arguments.
	 * @return the new converted arguments.  It will return the same array
	 * oldArgs if there were no changes.
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
		private final SubtreePosition mPos;

		public BuildApplicationTerm(final ApplicationTerm term, final SubtreePosition pos) {
			mAppTerm = term;
			mPos = pos;
		}

		@Override
		public void walk(final NonRecursive engine) {
			final PositionAwareTermTransformer transformer = (PositionAwareTermTransformer) engine;
			/* collect args and check if they have been changed */
			final Term[] oldArgs = mAppTerm.getParameters();
			final Term[] newArgs = transformer.getConverted(oldArgs);
			transformer.convertApplicationTerm(mAppTerm, newArgs, mPos);
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
		private final SubtreePosition mPos;

		public StartLetTerm(final LetTerm term, final SubtreePosition pos) {
			mLetTerm = term;
			mPos = pos;
		}

		@Override
		public void walk(final NonRecursive engine) {
			final PositionAwareTermTransformer transformer = (PositionAwareTermTransformer) engine;
			final Term[] values = transformer.getConverted(mLetTerm.getValues());
			transformer.preConvertLet(mLetTerm, values, mPos);
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
		private final SubtreePosition mPos;

		public BuildLetTerm(final LetTerm term, final Term[] newValues, final SubtreePosition pos) {
			mLetTerm = term;
			mNewValues = newValues;
			mPos = pos;
		}

		@Override
		public void walk(final NonRecursive engine) {
			final PositionAwareTermTransformer transformer = (PositionAwareTermTransformer) engine;
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
		private final SubtreePosition mPos;

		public BuildQuantifier(final QuantifiedFormula term, final SubtreePosition pos) {
			mQuant = term;
			mPos = pos;
		}

		@Override
		public void walk(final NonRecursive engine) {
			final PositionAwareTermTransformer transformer = (PositionAwareTermTransformer) engine;
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
		private final SubtreePosition mPos;

		public BuildAnnotation(final AnnotatedTerm term, final SubtreePosition pos) {
			mAnnotatedTerm = term;
			mPos = pos;
		}

		@Override
		public void walk(final NonRecursive engine) {
			final PositionAwareTermTransformer transformer = (PositionAwareTermTransformer) engine;
			final Annotation[] annots = mAnnotatedTerm.getAnnotations();
			Annotation[] newAnnots = annots;
			for (int i = annots.length - 1; i >= 0; i--) {
				final Object value = annots[i].getValue();
				Object newValue;
				if (value instanceof Term) {
					newValue = transformer.getConverted();
				} else if (value instanceof Term[]) {
					newValue = transformer.getConverted((Term[]) value);
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

	@Override
	public void reset() {
		super.reset();
		mConverted.clear();
//		mCache.clear();
	}

}