package local.stalin.SMTInterface.z3interpol;

import local.stalin.SMTInterface.z3interpol.InterpolationInfoHolder.InterpolationException;
import local.stalin.logic.Formula;

public interface IInterpolationRule {
	public void install(IInterpolationRule[] repo);
	/**
	 * Creates a sequence of interpolants for a rule.
	 * @param numforms Number of interpolants to generate 
	 * @param rule Number of the proof rule.
	 * @param antecedents The antecedents.
	 * @param antinterpols The interpolants for the antecedents. First dimension is antecedent, Second is Interpolant.
	 * @param res The result formula.
	 * @param iih Interpolation information holder.
	 * @return Interpolants for the result formula.
	 */
	public Interpolants interpolate(int numforms,int rule,Formula[] antecedents,Interpolants[] antinterpols,
			Formula res,InterpolationInfoHolder iih) throws InterpolationException;
}
