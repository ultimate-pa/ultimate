package de.uni_freiburg.informatik.ultimate.plugins.analysis.abstractinterpretationMk2;

import java.util.Map;

import de.uni_freiburg.informatik.ultimate.logic.Term;
import de.uni_freiburg.informatik.ultimate.model.IElement;
import de.uni_freiburg.informatik.ultimate.model.annotation.ModernAnnotations;
import de.uni_freiburg.informatik.ultimate.model.annotation.Visualizable;
import de.uni_freiburg.informatik.ultimate.plugins.generator.rcfgbuilder.cfg.RCFGNode;

/**
 * @author Daniel Dietsch (dietsch@informatik.uni-freiburg.de)
 *
 */
public class AbstractInterpretationPredicates extends ModernAnnotations {

	private static final long serialVersionUID = 1L;

	private static final String ANNOTATION_NAME = AbstractInterpretationPredicates.class.getName();

	@Visualizable
	private final Map<RCFGNode, Term> mPredicates;

	protected AbstractInterpretationPredicates(Map<RCFGNode, Term> predicates) {
		mPredicates = predicates;
	}

	/**
	 * @return A set of predicates belonging to each program point that contains
	 *         terms representing the fixpoint found by AI at that program
	 *         location.
	 */
	public Map<RCFGNode, Term> getPredicates() {
		return mPredicates;
	}

	/**
	 * Annotate a given {@link IElement} with this
	 * {@link AbstractInterpretationPredicates} instance.
	 * 
	 * @param element
	 *            The {@link IElement} object this annotation shall be added to
	 */
	public void annotate(IElement element) {
		element.getPayload().getAnnotations().put(ANNOTATION_NAME, this);
	}

	/**
	 * Checks the given {@link IElement} for an
	 * {@link AbstractInterpretationPredicates} and returns it
	 * 
	 * @param element
	 *            The element whose Annotation is to be retrieved
	 * @return An {@link AbstractInterpretationPredicates} on the
	 *         {@link IElement} or null if none is present
	 */
	public static AbstractInterpretationPredicates getAnnotation(IElement element) {
		if (!element.hasPayload()) {
			return null;
		}
		if (!element.getPayload().hasAnnotation()) {
			return null;
		}
		return (AbstractInterpretationPredicates) element.getPayload().getAnnotations().get(ANNOTATION_NAME);
	}

	@Override
	public String toString() {
		return ANNOTATION_NAME;
	}
}
