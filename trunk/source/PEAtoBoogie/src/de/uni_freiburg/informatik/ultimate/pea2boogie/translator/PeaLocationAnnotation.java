package de.uni_freiburg.informatik.ultimate.pea2boogie.translator;

import java.util.List;

import de.uni_freiburg.informatik.ultimate.core.lib.models.annotation.ModernAnnotations;
import de.uni_freiburg.informatik.ultimate.core.model.models.IElement;
import de.uni_freiburg.informatik.ultimate.core.model.models.ModelUtils;
import de.uni_freiburg.informatik.ultimate.core.model.models.annotation.IAnnotations;
import de.uni_freiburg.informatik.ultimate.lib.pea.Phase;
import de.uni_freiburg.informatik.ultimate.lib.pea.PhaseEventAutomata;
import de.uni_freiburg.informatik.ultimate.util.datastructures.DataStructureUtils;


public class PeaLocationAnnotation extends ModernAnnotations {

	private final List<Phase> mLocation;
	private final List<PhaseEventAutomata> mAutomaton;

	public PeaLocationAnnotation(final List<PhaseEventAutomata> aut, final List<Phase> location) {
		mLocation = location;
		mAutomaton = aut;
	}

	public  List<Phase> getLocation() {
		return mLocation;
	}

	public List<PhaseEventAutomata> getAutomaton() {
		return mAutomaton;
	}

	public IAnnotations annotate(final IElement elem) {
		return elem.getPayload().getAnnotations().put(PeaLocationAnnotation.class.getName(), this);
	}

	public static PeaLocationAnnotation getAnnotation(final IElement node) {
		return ModelUtils.getAnnotation(node, PeaLocationAnnotation.class);
	}

	@Override
	public IAnnotations merge(final IAnnotations other) {
		if (other instanceof PeaLocationAnnotation) {
			return new PeaLocationAnnotation(DataStructureUtils.concat(mAutomaton, ((PeaLocationAnnotation) other).getAutomaton()),
					DataStructureUtils.concat(mLocation, ((PeaLocationAnnotation) other).getLocation()));
		}
		return super.merge(other);
	}

}
