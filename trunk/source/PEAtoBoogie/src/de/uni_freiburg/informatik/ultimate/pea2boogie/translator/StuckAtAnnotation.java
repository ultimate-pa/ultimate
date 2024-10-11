package de.uni_freiburg.informatik.ultimate.pea2boogie.translator;

import java.util.List;

import de.uni_freiburg.informatik.ultimate.core.lib.models.annotation.ModernAnnotations;
import de.uni_freiburg.informatik.ultimate.core.model.models.IElement;
import de.uni_freiburg.informatik.ultimate.core.model.models.ModelUtils;
import de.uni_freiburg.informatik.ultimate.core.model.models.annotation.IAnnotations;
import de.uni_freiburg.informatik.ultimate.lib.pea.Phase;

/**
 * 
 * Preliminary Annotation for stuck at checks. This marks the non-terminal violable phase (nvp) for which the check is executed.
 *
 */

public class StuckAtAnnotation extends ModernAnnotations {

	private static final long serialVersionUID = 1L;
	private final List<Phase> mNvp;

	public StuckAtAnnotation(final List<Phase> nvp) {
		mNvp = nvp;
	}

	public List<Phase> getNvp() {
		return mNvp;
	}

	public IAnnotations annotate(final IElement elem) {
		return elem.getPayload().getAnnotations().put(StuckAtAnnotation.class.getName(), this);
	}

	public static StuckAtAnnotation getAnnotation(final IElement node) {
		return ModelUtils.getAnnotation(node, StuckAtAnnotation.class);
	}
}