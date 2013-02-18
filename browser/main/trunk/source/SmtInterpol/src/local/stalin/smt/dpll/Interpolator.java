package local.stalin.smt.dpll;

public interface Interpolator {

	public InterpolationInfo interpolate(DPLLEngine engine, DPLLAtom atom,
			int fnr, InterpolationInfo interpolationInfo, InterpolationInfo otherInfo);

	public Interpolator merge(Interpolator other);
}
