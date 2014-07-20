/**
 * 
 */
package de.uni_freiburg.informatik.ultimate.plugins.analysis.abstractinterpretation.abstractdomain.signdomain;

import de.uni_freiburg.informatik.ultimate.plugins.analysis.abstractinterpretation.AbstractInterpreter;
import de.uni_freiburg.informatik.ultimate.plugins.analysis.abstractinterpretation.abstractdomain.AbstractDomainRegistry;
import de.uni_freiburg.informatik.ultimate.plugins.analysis.abstractinterpretation.abstractdomain.IAbstractDomainFactory;
import de.uni_freiburg.informatik.ultimate.plugins.analysis.abstractinterpretation.abstractdomain.IMergeOperator;
import de.uni_freiburg.informatik.ultimate.plugins.analysis.abstractinterpretation.abstractdomain.IWideningOperator;
import de.uni_freiburg.informatik.ultimate.plugins.analysis.abstractinterpretation.abstractdomain.signdomain.SignValue.Sign;

/**
 * @author Christopher Dillo
 *
 */
public class SignDomainFactory implements IAbstractDomainFactory {

	public static final String s_DomainID = "SIGN";
	
	/* (non-Javadoc)
	 * @see de.uni_freiburg.informatik.ultimate.plugins.analysis.abstractinterpretation.abstractdomain.IAbstractDomainFactory#getDomainID()
	 */
	@Override
	public String getDomainID() {
		return s_DomainID;
	}

	/* (non-Javadoc)
	 * @see de.uni_freiburg.informatik.ultimate.plugins.analysis.abstractinterpretation.abstractdomain.IAbstractDomainFactory#makeTopValue()
	 */
	@Override
	public SignValue makeTopValue() {
		return new SignValue(Sign.PLUSMINUS);
	}

	/* (non-Javadoc)
	 * @see de.uni_freiburg.informatik.ultimate.plugins.analysis.abstractinterpretation.abstractdomain.IAbstractDomainFactory#makeBottomValue()
	 */
	@Override
	public SignValue makeBottomValue() {
		return new SignValue(Sign.ZERO);
	}

	/* (non-Javadoc)
	 * @see de.uni_freiburg.informatik.ultimate.plugins.analysis.abstractinterpretation.abstractdomain.IAbstractDomainFactory#makeIntegerValue(int)
	 */
	@Override
	public SignValue makeIntegerValue(String integer) {
		// TODO: Representation of integers as a string??
		
		if (integer.equals("0"))
			return new SignValue(Sign.ZERO);
		
		if (integer.startsWith("-"))
			return new SignValue(Sign.MINUS);
		
		return new SignValue(Sign.PLUS);
	}

	/* (non-Javadoc)
	 * @see de.uni_freiburg.informatik.ultimate.plugins.analysis.abstractinterpretation.abstractdomain.IAbstractDomainFactory#makeIntegerValue(int)
	 */
	@Override
	public SignValue makeRealValue(String real) {
		// TODO: Representation of reals as a string??
		
		if (real.equals("0"))
			return new SignValue(Sign.ZERO);
		
		if (real.startsWith("-"))
			return new SignValue(Sign.MINUS);
		
		return new SignValue(Sign.PLUS);
	}

	/* (non-Javadoc)
	 * @see de.uni_freiburg.informatik.ultimate.plugins.analysis.abstractinterpretation.abstractdomain.IAbstractDomainFactory#makeWideningOperator()
	 */
	@Override
	public IWideningOperator makeWideningOperator() {
		IWideningOperator chosenOp;
		try {
			chosenOp = AbstractDomainRegistry.getWideningOperator(getDomainID(), AbstractInterpreter.getNumberWideningOperatorName()).newInstance();
		} catch (InstantiationException | IllegalAccessException e) {
			e.printStackTrace();
			return null;
		}
		
		return chosenOp;
	}

	/* (non-Javadoc)
	 * @see de.uni_freiburg.informatik.ultimate.plugins.analysis.abstractinterpretation.abstractdomain.IAbstractDomainFactory#makeMergeOperator()
	 */
	@Override
	public IMergeOperator makeMergeOperator() {
		IMergeOperator chosenOp;
		try {
			chosenOp = AbstractDomainRegistry.getMergeOperator(getDomainID(), AbstractInterpreter.getNumberMergeOperatorName()).newInstance();
		} catch (InstantiationException | IllegalAccessException e) {
			e.printStackTrace();
			return null;
		}
		
		return chosenOp;
	}

}
