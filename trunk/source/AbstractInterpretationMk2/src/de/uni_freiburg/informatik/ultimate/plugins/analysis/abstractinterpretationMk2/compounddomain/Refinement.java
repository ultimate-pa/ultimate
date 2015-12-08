package de.uni_freiburg.informatik.ultimate.plugins.analysis.abstractinterpretationMk2.compounddomain;

import de.uni_freiburg.informatik.ultimate.plugins.analysis.abstractinterpretationMk2.abstractdomain.IAbstractState;

/**
 * Refines an abstract state of type F (from) to type T (to)
 * 
 * @author GROSS-JAN
 *
 * @param <F>
 *            form
 * @param <T>
 *            to
 */
@SuppressWarnings({ "rawtypes", "unchecked" })
public abstract class Refinement<F, T> {
	private final Class<?> mFrom;
	private final Class<?> mTo;

	public Refinement(Class<?> from, Class<?> to) {
		mFrom = from;
		mTo = to;
	}

	public void refine(IAbstractState a, IAbstractState b) {
		if (mFrom.isInstance(a) && mTo.isInstance(b)) {
			refine((F) a, (T) b);
		} else if (mFrom.isInstance(b) && mTo.isInstance(a)) {
			refine((F) b, (T) a);
		}
	}

	protected abstract void refine(F f, T t);
}
