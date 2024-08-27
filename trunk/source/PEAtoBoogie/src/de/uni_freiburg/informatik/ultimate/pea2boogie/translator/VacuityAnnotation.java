package de.uni_freiburg.informatik.ultimate.pea2boogie.translator;

import de.uni_freiburg.informatik.ultimate.core.lib.models.annotation.ModernAnnotations;
import de.uni_freiburg.informatik.ultimate.core.model.models.IElement;
import de.uni_freiburg.informatik.ultimate.core.model.models.ModelUtils;
import de.uni_freiburg.informatik.ultimate.core.model.models.annotation.IAnnotations;
import de.uni_freiburg.informatik.ultimate.lib.pea.CDD;

/**
 * 
 * Annotation for vacuity checks. This marks whether a vacuous requirement
 * enforces a trivial invariant.
 *
 */

public class VacuityAnnotation extends ModernAnnotations {

	private static final long serialVersionUID = 1L;
	private final CDD mEnforcedInvariant;

	public VacuityAnnotation(final CDD enforcedInv) {
		mEnforcedInvariant = enforcedInv;
	}

	public CDD getInvariant() {
		return mEnforcedInvariant;
	}

	public IAnnotations annotate(final IElement elem) {
		return elem.getPayload().getAnnotations().put(VacuityAnnotation.class.getName(), this);
	}

	public static VacuityAnnotation getAnnotation(final IElement node) {
		return ModelUtils.getAnnotation(node, VacuityAnnotation.class);
	}
}
