package de.uni_freiburg.informatik.ultimate.cdt.translation.implementation.base.idps;

import de.uni_freiburg.informatik.ultimate.core.lib.models.annotation.ModernAnnotations;
import de.uni_freiburg.informatik.ultimate.core.model.models.IElement;
import de.uni_freiburg.informatik.ultimate.core.model.models.ModelUtils;
import de.uni_freiburg.informatik.ultimate.core.model.models.annotation.IAnnotations;

public class InterruptAnnotations extends ModernAnnotations {
	private static final long serialVersionUID = 1L;
	private final ISRLocation mIsrLocation;
	private final int mIsrId;

	public InterruptAnnotations(final ISRLocation isrLocation, final int isrId) {
		mIsrLocation = isrLocation;
		mIsrId = isrId;
	}

	public InterruptAnnotations annotate(final IElement element) {
		return (InterruptAnnotations) element.getPayload().getAnnotations().put(InterruptAnnotations.class.getName(),
				this);
	}

	public int getIsrId() {
		return mIsrId;
	}

	public ISRLocation getIsrLocation() {
		return mIsrLocation;
	}

	public static InterruptAnnotations getAnnotation(final IElement node) {
		return ModelUtils.getAnnotation(node, InterruptAnnotations.class);
	}

	@Override
	public IAnnotations merge(final IAnnotations other) {
		if (other == this || other == null) {
			return this;
		}
		if (!(other instanceof InterruptAnnotations)) {
			return super.merge(other);
		}
		final InterruptAnnotations otherAnnotations = (InterruptAnnotations) other;
		final var otherLoc = otherAnnotations.getIsrLocation();
		final var otherId = otherAnnotations.getIsrId();
		if (getIsrLocation().equals(otherLoc) && getIsrId() == otherId) {
			return other;
		}
		if (otherLoc == ISRLocation.ISR && getIsrLocation() == ISRLocation.MAIN) {
			return other;
		}
		if (otherLoc == ISRLocation.MAIN && getIsrLocation() == ISRLocation.ISR) {
			return this;
		}
		assert otherId == getIsrId();
		return this;
	}

	public static boolean hasAnnotation(final IElement node) {
		return ModelUtils.getAnnotation(node, InterruptAnnotations.class) != null;
	}

	public enum ISRLocation {
		ISR, MAIN
	}
}
