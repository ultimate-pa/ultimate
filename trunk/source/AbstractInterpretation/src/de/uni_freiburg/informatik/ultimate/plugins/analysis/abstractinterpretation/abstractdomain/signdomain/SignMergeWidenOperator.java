/**
 * 
 */
package de.uni_freiburg.informatik.ultimate.plugins.analysis.abstractinterpretation.abstractdomain.signdomain;

import de.uni_freiburg.informatik.ultimate.plugins.analysis.abstractinterpretation.abstractdomain.AbstractState;
import de.uni_freiburg.informatik.ultimate.plugins.analysis.abstractinterpretation.abstractdomain.IAbstractValue;
import de.uni_freiburg.informatik.ultimate.plugins.analysis.abstractinterpretation.abstractdomain.IMergeOperator;
import de.uni_freiburg.informatik.ultimate.plugins.analysis.abstractinterpretation.abstractdomain.IWideningOperator;
import de.uni_freiburg.informatik.ultimate.plugins.analysis.abstractinterpretation.abstractdomain.signdomain.SignValue.Sign;

/**
 * @author Christopher Dillo
 *
 */
public class SignMergeWidenOperator implements IWideningOperator, IMergeOperator {

	/* (non-Javadoc)
	 * @see de.uni_freiburg.informatik.ultimate.plugins.analysis.abstractinterpretation.abstractdomain.IWideningOperator#getDomainID()
	 */
	@Override
	public String getDomainID() {
		return SignDomainFactory.s_DomainID;
	}

	/* (non-Javadoc)
	 * @see de.uni_freiburg.informatik.ultimate.plugins.analysis.abstractinterpretation.abstractdomain.IWideningOperator#getName()
	 */
	@Override
	public String getName() {
		return "SIGN Merge & Widen";
	}

	/* (non-Javadoc)
	 * @see de.uni_freiburg.informatik.ultimate.plugins.analysis.abstractinterpretation.abstractdomain.IWideningOperator#apply(de.uni_freiburg.informatik.ultimate.plugins.analysis.abstractinterpretation.abstractdomain.IAbstractValue, de.uni_freiburg.informatik.ultimate.plugins.analysis.abstractinterpretation.abstractdomain.IAbstractValue)
	 */
	@Override
	public SignValue apply(IAbstractValue oldValue, IAbstractValue newValue) {
		SignValue oldSignValue = (SignValue) oldValue;
		SignValue newSignValue = (SignValue) newValue; 
		
		// invalid state objects
		if ((oldSignValue == null) || (newSignValue == null)) {
			return null;
		}

		// old is PLUSMINUS : PLUSMINUS
		if (oldSignValue.isTop())
			return new SignValue(Sign.PLUSMINUS);
		
		// new is PLUSMINUS : PLUSMINUS
		if (newSignValue.isTop())
			return new SignValue(Sign.PLUSMINUS);
		
		Sign oldV = oldSignValue.getValue();
		Sign newV = newSignValue.getValue();
		
		// old is ZERO : new
		if (oldSignValue.isBottom())
			return new SignValue(newV);

		// new is ZERO : old
		if (newSignValue.isBottom())
			return new SignValue(oldV);
		
		// old is new : old (or new)
		if (oldV == newV)
			return new SignValue(oldV);
		
		// old is PLUS, new is MINUS or vice versa : PLUSMINUS
		return new SignValue(Sign.PLUSMINUS);
	}

}
